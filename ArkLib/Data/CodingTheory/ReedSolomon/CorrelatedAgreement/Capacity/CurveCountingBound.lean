/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.CountingBound
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.Parameters
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.RegularEquation

/-!
# Elementary budgets for polynomial-curve correlated agreement

The two polynomial-curve cut ratios are linear in the block length.  The main estimate below
retains the actual separant-stage order and displays the lifted source-degree prefactor
explicitly.  In particular, it does not conceal the extra factor contributed by a Taylor cutoff
which may grow with the block length.
-/

namespace ReedSolomon

/-- A common scale for the incidence and retained-tuple cut ratios. -/
noncomputable def polynomialCurveChartScale (δ : ℝ) (v : ℕ) : ℝ :=
  2 * (2 + 2 * (v : ℝ)) / δ

/-- Either polynomial-curve cut degree is at most a constant times the block length. -/
theorem polynomialCurveCutDegree_le (n K v c : ℕ) (hn : 0 < n) (hKn : K ≤ n)
    (hc : c ≤ 2) :
    c + 2 * K * (v - 1) ≤ n * (2 + 2 * v) := by
  have hone : 1 ≤ n := hn
  have hconst : c ≤ n * 2 := hc.trans (Nat.le_mul_of_pos_left 2 hn)
  have htail : 2 * K * (v - 1) ≤ n * (2 * v) := by
    have hv : v - 1 ≤ v := Nat.sub_le _ _
    calc
      2 * K * (v - 1) ≤ 2 * n * v := Nat.mul_le_mul
        (Nat.mul_le_mul_left 2 hKn) hv
      _ = n * (2 * v) := by ac_rfl
  calc
    c + 2 * K * (v - 1) ≤ n * 2 + n * (2 * v) := Nat.add_le_add hconst htail
    _ = n * (2 + 2 * v) := by simp [Nat.mul_add]

/-- Dividing either polynomial-curve cut by a midpoint half-gap leaves one block-length
factor. -/
theorem polynomialCurveCutRatio_le (δ : ℝ) (n K v D c : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hKn : K ≤ n) (hc : c ≤ 2)
    (hD : δ * n / 2 ≤ (D : ℝ)) :
    ((n * (c + 2 * K * (v - 1)) : ℕ) : ℝ) / D ≤
      polynomialCurveChartScale δ v * n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hD
  have hb : ((c + 2 * K * (v - 1) : ℕ) : ℝ) ≤
      n * (2 + 2 * (v : ℝ)) := by
    exact_mod_cast polynomialCurveCutDegree_le n K v c hn hKn hc
  have hscale : 0 ≤ polynomialCurveChartScale δ v := by
    unfold polynomialCurveChartScale
    positivity
  apply (div_le_iff₀ hDpos).mpr
  have hm := mul_le_mul_of_nonneg_left hD
    (mul_nonneg hscale hn'.le)
  have he : polynomialCurveChartScale δ v * n * (δ * n / 2) =
      (n : ℝ) * (n * (2 + 2 * (v : ℝ))) := by
    unfold polynomialCurveChartScale
    field_simp
  rw [he] at hm
  apply le_trans ?_ hm
  simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hb hn'.le

/-! ## Corrected chunked-lift scalar bounds -/

/-- The chunked-lift source cut degree is at most a gap-dependent constant times the block
length. -/
theorem polynomialCurve_correctedCutDegree_le (n K v : ℕ) (hn : 0 < n) (hKn : K ≤ n) :
    2 + 2 * K * v ≤ n * (2 + 2 * v) := by
  have hconst : 2 ≤ n * 2 := Nat.le_mul_of_pos_left 2 hn
  have htail : 2 * K * v ≤ n * (2 * v) := by
    calc
      2 * K * v ≤ 2 * n * v := Nat.mul_le_mul_right v (Nat.mul_le_mul_left 2 hKn)
      _ = n * (2 * v) := by ac_rfl
  calc
    2 + 2 * K * v ≤ n * 2 + n * (2 * v) := Nat.add_le_add hconst htail
    _ = n * (2 + 2 * v) := by simp [Nat.mul_add]

/-- Dividing the corrected chunked-lift source cut by the upper midpoint gap leaves one
block-length factor. -/
theorem polynomialCurve_correctedCutRatio_le (δ : ℝ) (n K v D : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hKn : K ≤ n)
    (hD : δ * n / 2 ≤ (D : ℝ)) :
    ((n * (2 + 2 * K * v) : ℕ) : ℝ) / D ≤ polynomialCurveChartScale δ v * n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hD
  have hb : ((2 + 2 * K * v : ℕ) : ℝ) ≤ n * (2 + 2 * (v : ℝ)) := by
    exact_mod_cast polynomialCurve_correctedCutDegree_le n K v hn hKn
  have hscale : 0 ≤ polynomialCurveChartScale δ v := by
    unfold polynomialCurveChartScale
    positivity
  apply (div_le_iff₀ hDpos).mpr
  have hm := mul_le_mul_of_nonneg_left hD (mul_nonneg hscale hn'.le)
  have he : polynomialCurveChartScale δ v * n * (δ * n / 2) =
      (n : ℝ) * (n * (2 + 2 * (v : ℝ))) := by
    unfold polynomialCurveChartScale
    field_simp
  rw [he] at hm
  apply le_trans ?_ hm
  simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hb hn'.le

/-- With challenge height `338ℓv-1`, the corrected source degree `ℓ+H` is linear in `ℓ`
with no block-length loss. -/
theorem polynomialCurve_correctedSourceDegree_le (ℓ v : ℕ) :
    ((ℓ + (338 * (ℓ * v) - 1) : ℕ) : ℝ) ≤ (ℓ : ℝ) * (1 + 338 * v) := by
  have hheightNat : 338 * (ℓ * v) - 1 ≤ 338 * (ℓ * v) := Nat.sub_le _ _
  have hheight : ((338 * (ℓ * v) - 1 : ℕ) : ℝ) ≤ 338 * (ℓ : ℝ) * v := by
    have hheight' : ((338 * (ℓ * v) - 1 : ℕ) : ℝ) ≤
        ((338 * (ℓ * v) : ℕ) : ℝ) := by exact_mod_cast hheightNat
    calc
      _ ≤ ((338 * (ℓ * v) : ℕ) : ℝ) := hheight'
      _ = 338 * (ℓ : ℝ) * v := by push_cast; ring
  rw [Nat.cast_add]
  calc
    (ℓ : ℝ) + (338 * (ℓ * v) - 1 : ℕ) ≤ ℓ + 338 * ℓ * v :=
      add_le_add le_rfl hheight
    _ = (ℓ : ℝ) * (1 + 338 * v) := by ring

/-- A convenient coefficient for the corrected finite-stage polynomial-curve budget. -/
noncomputable def polynomialCurveUniformMCAConstant (δ : ℝ) (v d : ℕ) : ℝ :=
  (338 * v : ℕ) + v * (((1 + 338 * v : ℕ) : ℝ) * (v + 1) + v) *
    (max 1 (polynomialCurveChartScale δ v)) ^ (d + 1)

/-- The gap-only specialization of the corrected polynomial-curve MCA coefficient. -/
noncomputable def prescribedCurveMCAConstant (δ : ℝ) : ℝ :=
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
  let v := 2 * m - 1
  polynomialCurveUniformMCAConstant δ v d

/-- The corrected actual-order stage expression.  Unlike the earlier coarse source-degree
estimate, its lifted prefactor does not contain `K`. -/
noncomputable def correctedPolynomialCurveStageBound
    (δ : ℝ) (n ℓ v H r : ℕ) : ℝ :=
  ((((ℓ + H : ℕ) : ℝ) * (v + 1) *
      polynomialCurveChartScale δ v ^ (r + 1) +
    (ℓ : ℝ) * v * polynomialCurveChartScale δ v ^ r) *
      (n : ℝ) ^ (r + 1))

/-- The corrected midpoint estimate before uniformizing the actual stage order. -/
theorem polynomialCurve_correctedActualOrder_budget (δ : ℝ)
    (n K k A ℓ v r : ℕ) (hδ : 0 < δ) (hn : 0 < n) (hKn : K ≤ n)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    let L := correlatedMidpoint δ n k
    let H := 338 * (ℓ * v) - 1
    (((ℓ + H : ℕ) : ℝ) * ((v + 1 : ℕ) : ℝ) *
        (((n * (2 + 2 * K * v) : ℕ) : ℝ) /
          ((A - L + 1 : ℕ) : ℝ)) ^ (r + 1) +
      ((ℓ * (n - L) : ℕ) : ℝ) * (v : ℝ) *
        (((n * (1 + 2 * K * (v - 1)) : ℕ) : ℝ) /
          ((L - k + 1 : ℕ) : ℝ)) ^ r) ≤
      correctedPolynomialCurveStageBound δ n ℓ v H r := by
  dsimp only
  let L := correlatedMidpoint δ n k
  have hL := correlatedMidpoint_bounds δ n k A hδ.le hgap hAn
  have hmain := polynomialCurve_correctedCutRatio_le δ n K v (A - L + 1)
    hδ hn hKn hL.2.2.2.1
  have hretained := polynomialCurveCutRatio_le δ n K v (L - k + 1) 1
    hδ hn hKn (by omega) hL.2.2.2.2
  have hmainPow := pow_le_pow_left₀ (by positivity) hmain (r + 1)
  have hretainedPow := pow_le_pow_left₀ (by positivity) hretained r
  have hfirst := mul_le_mul
    (le_refl (((ℓ + (338 * (ℓ * v) - 1) : ℕ) : ℝ) * ((v + 1 : ℕ) : ℝ)))
    hmainPow (by positivity) (by positivity)
  have hnL : (((n - L : ℕ) : ℝ)) ≤ n := by exact_mod_cast Nat.sub_le n L
  have hsecondLeft : ((ℓ * (n - L) : ℕ) : ℝ) * (v : ℝ) ≤
      (ℓ : ℝ) * n * v := by
    push_cast
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnL (Nat.cast_nonneg ℓ)) (Nat.cast_nonneg v)
  have hsecond := mul_le_mul hsecondLeft hretainedPow (by positivity) (by positivity)
  calc
    _ ≤ (((ℓ + (338 * (ℓ * v) - 1) : ℕ) : ℝ) * ((v + 1 : ℕ) : ℝ)) *
          (polynomialCurveChartScale δ v * n) ^ (r + 1) +
        ((ℓ : ℝ) * n * v) * (polynomialCurveChartScale δ v * n) ^ r :=
      add_le_add hfirst hsecond
    _ = correctedPolynomialCurveStageBound δ n ℓ v (338 * (ℓ * v) - 1) r := by
      unfold correctedPolynomialCurveStageBound
      simp only [mul_pow, pow_succ]
      push_cast
      ring

/-- The corrected regular-chart budget at the midpoint threshold, retaining the actual stage
order. -/
theorem regularSymbolicCurveMCABound_midpoint_le (δ : ℝ)
    (n K k A ℓ v r : ℕ) (hδ : 0 < δ) (hn : 0 < n) (hKn : K ≤ n)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    let L := correlatedMidpoint δ n k
    let H := 338 * (ℓ * v) - 1
    (regularSymbolicCurveMCABound n r ℓ K k L A v H : ℝ) ≤
      correctedPolynomialCurveStageBound δ n ℓ v H r := by
  have hb := polynomialCurve_correctedActualOrder_budget
    δ n K k A ℓ v r hδ hn hKn hgap hAn
  unfold regularSymbolicCurveMCABound
  push_cast at hb ⊢
  simpa only [mul_assoc] using hb

/-- Corrected finite-stage uniformization.  The coefficient is independent of `n`, `K`, and
`ℓ`; the batching degree stays linear and the certificate derivative cap `d` gives exactly
`n^(d+1)`. -/
theorem polynomialCurve_correctedFiniteStage_budget {ι : Type*} (S : Finset ι)
    (order : ι → ℕ) (cost : ι → ℝ) (δ : ℝ) (n ℓ v d : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hcard : S.card ≤ v)
    (horder : ∀ i ∈ S, order i ≤ d)
    (hcost : ∀ i ∈ S, cost i ≤ correctedPolynomialCurveStageBound δ n ℓ v
      (338 * (ℓ * v) - 1) (order i)) :
    ((338 * (ℓ * v) - 1 : ℕ) : ℝ) + ∑ i ∈ S, cost i ≤
      (ℓ : ℝ) * polynomialCurveUniformMCAConstant δ v d * (n : ℝ) ^ (d + 1) := by
  let c := polynomialCurveChartScale δ v
  let C := max 1 c
  let T : ℝ := (((1 + 338 * v : ℕ) : ℝ) * (v + 1) + v) * C ^ (d + 1)
  have hc : 0 ≤ c := by dsimp [c, polynomialCurveChartScale]; positivity
  have hC : 1 ≤ C := le_max_left _ _
  have hsource := polynomialCurve_correctedSourceDegree_le ℓ v
  have hstage (i : ι) (hi : i ∈ S) : cost i ≤
      (ℓ : ℝ) * T * (n : ℝ) ^ (d + 1) := by
    let r := order i
    have hr : r ≤ d := horder i hi
    have hcpow (j : ℕ) (hj : j ≤ d + 1) : c ^ j ≤ C ^ (d + 1) :=
      (pow_le_pow_left₀ hc (le_max_right _ _) j).trans (pow_le_pow_right₀ hC hj)
    have hnpow : (n : ℝ) ^ (r + 1) ≤ n ^ (d + 1) := by
      exact pow_le_pow_right₀ (by exact_mod_cast hn) (Nat.add_le_add_right hr 1)
    have hgeomMain : c ^ (r + 1) * (n : ℝ) ^ (r + 1) ≤
        C ^ (d + 1) * (n : ℝ) ^ (d + 1) :=
      mul_le_mul (hcpow (r + 1) (Nat.add_le_add_right hr 1)) hnpow
        (by positivity) (by positivity)
    have hgeomRetained : c ^ r * (n : ℝ) ^ (r + 1) ≤
        C ^ (d + 1) * (n : ℝ) ^ (d + 1) :=
      mul_le_mul (hcpow r (hr.trans (Nat.le_succ d))) hnpow
        (by positivity) (by positivity)
    have hfirst := mul_le_mul
      (mul_le_mul_of_nonneg_right hsource (show (0 : ℝ) ≤ (v : ℝ) + 1 by positivity))
      hgeomMain (by positivity) (by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hgeomRetained
      (show (0 : ℝ) ≤ (ℓ : ℝ) * v by positivity)
    calc
      cost i ≤ correctedPolynomialCurveStageBound δ n ℓ v
          (338 * (ℓ * v) - 1) r := hcost i hi
      _ = (((ℓ + (338 * (ℓ * v) - 1) : ℕ) : ℝ) * (v + 1)) *
            (c ^ (r + 1) * (n : ℝ) ^ (r + 1)) +
          ((ℓ : ℝ) * v) * (c ^ r * (n : ℝ) ^ (r + 1)) := by
        unfold correctedPolynomialCurveStageBound
        dsimp only [c]
        ring
      _ ≤ ((ℓ : ℝ) * (1 + 338 * v) * (v + 1)) *
            (C ^ (d + 1) * (n : ℝ) ^ (d + 1)) +
          ((ℓ : ℝ) * v) * (C ^ (d + 1) * (n : ℝ) ^ (d + 1)) := by
        exact add_le_add hfirst hsecond
      _ = (ℓ : ℝ) * T * (n : ℝ) ^ (d + 1) := by
        dsimp only [T]
        push_cast
        ring
  have hT : 0 ≤ T := by dsimp [T, C]; positivity
  have hsum : ∑ i ∈ S, cost i ≤
      (v : ℝ) * ((ℓ : ℝ) * T * (n : ℝ) ^ (d + 1)) := by
    calc
      _ ≤ ∑ _i ∈ S, ((ℓ : ℝ) * T * (n : ℝ) ^ (d + 1)) :=
        Finset.sum_le_sum hstage
      _ = (S.card : ℝ) * ((ℓ : ℝ) * T * (n : ℝ) ^ (d + 1)) := by simp
      _ ≤ (v : ℝ) * ((ℓ : ℝ) * T * (n : ℝ) ^ (d + 1)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcard
        · positivity
  have hheightOnly : ((338 * (ℓ * v) - 1 : ℕ) : ℝ) ≤ (ℓ : ℝ) * (338 * v) := by
    have hnat : 338 * (ℓ * v) - 1 ≤ 338 * (ℓ * v) := Nat.sub_le _ _
    have hcast : ((338 * (ℓ * v) - 1 : ℕ) : ℝ) ≤
        ((338 * (ℓ * v) : ℕ) : ℝ) := by exact_mod_cast hnat
    calc
      _ ≤ ((338 * (ℓ * v) : ℕ) : ℝ) := hcast
      _ = (ℓ : ℝ) * (338 * v) := by push_cast; ring
  have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ (d + 1) :=
    one_le_pow₀ (by exact_mod_cast hn)
  have hterminal : ((338 * (ℓ * v) - 1 : ℕ) : ℝ) ≤
      (ℓ : ℝ) * (338 * v) * (n : ℝ) ^ (d + 1) :=
    hheightOnly.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hnPow
        (show (0 : ℝ) ≤ (ℓ : ℝ) * (338 * v) by positivity))
  calc
    _ ≤ (ℓ : ℝ) * (338 * v) * (n : ℝ) ^ (d + 1) +
        (v : ℝ) * ((ℓ : ℝ) * T * (n : ℝ) ^ (d + 1)) :=
      add_le_add hterminal hsum
    _ = (ℓ : ℝ) * polynomialCurveUniformMCAConstant δ v d *
        (n : ℝ) ^ (d + 1) := by
      unfold polynomialCurveUniformMCAConstant
      dsimp only [T, C]
      push_cast
      ring

/-- The corrected certificate-shaped stage sum has a coefficient independent of `n`, `K`, and
`ℓ`, is linear in `ℓ`, and has exponent exactly `d+1`. -/
theorem regularSymbolicCurveMCA_finiteStage_uniform_le {ι : Type*} (S : Finset ι)
    (order : ι → ℕ) (δ : ℝ) (n K k A ℓ v d : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hKn : K ≤ n)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (hcard : S.card ≤ v) (horder : ∀ i ∈ S, order i ≤ d) :
    let L := correlatedMidpoint δ n k
    let H := 338 * (ℓ * v) - 1
    (H : ℝ) + ∑ i ∈ S,
        (regularSymbolicCurveMCABound n (order i) ℓ K k L A v H : ℝ) ≤
      (ℓ : ℝ) * polynomialCurveUniformMCAConstant δ v d * (n : ℝ) ^ (d + 1) := by
  dsimp only
  apply polynomialCurve_correctedFiniteStage_budget S order
    (fun i ↦ (regularSymbolicCurveMCABound n (order i) ℓ K k
      (correlatedMidpoint δ n k) A v (338 * (ℓ * v) - 1) : ℝ))
    δ n ℓ v d hδ hn hcard horder
  intro i _hi
  exact regularSymbolicCurveMCABound_midpoint_le δ n K k A ℓ v (order i)
    hδ hn hKn hgap hAn

/-- Gap-only specialization of the corrected certificate-stage budget. -/
theorem prescribedCurveMCA_finiteStage_uniform_le {ι : Type*} (S : Finset ι)
    (order : ι → ℕ) (δ : ℝ) (n K k A ℓ : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hKn : K ≤ n)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
    let v := 2 * m - 1
    let L := correlatedMidpoint δ n k
    let H := 338 * (ℓ * v) - 1
    S.card ≤ v →
    (∀ i ∈ S, order i ≤ d) →
    (H : ℝ) + ∑ i ∈ S,
        (regularSymbolicCurveMCABound n (order i) ℓ K k L A v H : ℝ) ≤
      (ℓ : ℝ) * prescribedCurveMCAConstant δ * (n : ℝ) ^ (d + 1) := by
  dsimp only
  intro hcard horder
  exact regularSymbolicCurveMCA_finiteStage_uniform_le S order δ n K k A ℓ
    (2 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((169 / 25) / δ)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((169 / 25) / δ)) - 1)) - 1)
    (Nat.ceil (Real.exp ((169 / 25) / δ))) hδ hn hKn hgap hAn hcard horder

end ReedSolomon
