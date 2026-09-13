/-
Copyright (c) 2026 Gary Irving and ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gary Irving, Quang Dao

The Fourier and weighted-Young argument is adapted from
https://github.com/girving/aks/tree/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG.

The sharp estimate is due to Ofer Gabber and Zvi Galil, "Explicit Constructions of
Linear-Sized Superconcentrators", JCSS 22(3):407--420 (1981),
https://doi.org/10.1016/0022-0000(81)90040-4.
-/
module

public import ArkLib.Data.Graph.GabberGalilConstruction.EnergyEstimate.Assembly
public import Mathlib.Tactic.FinCases

/-!
# The exact Gabber--Galil energy estimate

For every positive side length, including composite side lengths, the eight labelled affine maps
have squared mean-zero adjacency norm at most `50`. The proof for side length at least three is
the discrete Fourier form of the Gabber--Galil/Jimbo--Maruoka argument: Parseval transfers the
four forward correlations to dual shears, and reciprocal Young weights give the sharp
`5 * sqrt 2` adjacency bound.
-/

@[expose] public section

namespace GabberGalil.EnergyEstimate

open scoped BigOperators Real
open Finset Real

private theorem finEquiv_eq_natCast (n : ℕ) [NeZero n] (x : Fin n) :
    ZMod.finEquiv n x = (x.val : ZMod n) := by
  rw [← ZMod.natCast_zmod_val (ZMod.finEquiv n x)]
  congr 1
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

private def vertexEquiv (n : ℕ) [NeZero n] : Fin n × Fin n ≃ Vertex n :=
  (ZMod.finEquiv n).toEquiv.prodCongr (ZMod.finEquiv n).toEquiv

private theorem sum_reindex (n : ℕ) [NeZero n] (h : Vertex n → ℝ) :
    ∑ v, h v = ∑ x : Fin n, ∑ y : Fin n, h ((x.val : ZMod n), (y.val : ZMod n)) := by
  rw [← (vertexEquiv n).sum_comp h, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  change h (ZMod.finEquiv n x, ZMod.finEquiv n y) = _
  rw [finEquiv_eq_natCast, finEquiv_eq_natCast]

private theorem step_zero_fin (n : ℕ) [NeZero n] (x y : Fin n) :
    step (m := n) (0 : Label) ((x.val : ZMod n), (y.val : ZMod n)) =
      ((((x.val + 2 * y.val) % n : ℕ) : ZMod n), (y.val : ZMod n)) := by
  change ((x.val : ZMod n) + 2 * (y.val : ZMod n), (y.val : ZMod n)) = _
  congr 1
  rw [ZMod.natCast_mod]
  push_cast
  ring

private theorem step_two_fin (n : ℕ) [NeZero n] (x y : Fin n) :
    step (m := n) (2 : Label) ((x.val : ZMod n), (y.val : ZMod n)) =
      ((((x.val + 2 * y.val + 1) % n : ℕ) : ZMod n), (y.val : ZMod n)) := by
  change ((x.val : ZMod n) + (2 * (y.val : ZMod n) + 1), (y.val : ZMod n)) = _
  congr 1
  rw [ZMod.natCast_mod]
  push_cast
  ring

private theorem step_four_fin (n : ℕ) [NeZero n] (x y : Fin n) :
    step (m := n) (4 : Label) ((x.val : ZMod n), (y.val : ZMod n)) =
      ((x.val : ZMod n), (((2 * x.val + y.val) % n : ℕ) : ZMod n)) := by
  change ((x.val : ZMod n), (y.val : ZMod n) + 2 * (x.val : ZMod n)) = _
  congr 1
  rw [ZMod.natCast_mod]
  push_cast
  ring

private theorem step_six_fin (n : ℕ) [NeZero n] (x y : Fin n) :
    step (m := n) (6 : Label) ((x.val : ZMod n), (y.val : ZMod n)) =
      ((x.val : ZMod n), (((2 * x.val + y.val + 1) % n : ℕ) : ZMod n)) := by
  change ((x.val : ZMod n), (y.val : ZMod n) + (2 * (x.val : ZMod n) + 1)) = _
  congr 1
  rw [ZMod.natCast_mod]
  push_cast
  ring

private theorem quadratic_reverse {n : ℕ} [NeZero n] (f : Vertex n → ℝ) (l : Label) :
    (∑ v, f v * f (step (reverseLabel l) v)) = ∑ v, f v * f (step l v) := by
  calc
    (∑ v, f v * f (step (reverseLabel l) v)) =
        ∑ v, f (step l v) * f v := (sum_mul_step l f f).symm
    _ = ∑ v, f v * f (step l v) := by
      apply Finset.sum_congr rfl
      intro v _
      ring

private theorem dot_adjacency_eq_correlations (n : ℕ) [NeZero n]
    (f : Vertex n → ℝ) :
    let g : Fin n → Fin n → ℝ :=
      fun x y => f ((x.val : ZMod n), (y.val : ZMod n))
    dot f (adjacency f) =
      2 * ((∑ x, ∑ y,
        g x y * (g ⟨(x.val + 2 * y.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩ y +
          g ⟨(x.val + 2 * y.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ y)) +
        ∑ x, ∑ y,
        g x y * (g x ⟨(2 * x.val + y.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩ +
          g x ⟨(2 * x.val + y.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)) := by
  intro g
  let q : Label → ℝ := fun l => ∑ v, f v * f (step l v)
  have hsum : dot f (adjacency f) = ∑ l, q l := by
    simp only [dot, adjacency, q, Finset.mul_sum]
    rw [Finset.sum_comm]
  have h10 : q 1 = q 0 := quadratic_reverse f 0
  have h32 : q 3 = q 2 := quadratic_reverse f 2
  have h54 : q 5 = q 4 := quadratic_reverse f 4
  have h76 : q 7 = q 6 := quadratic_reverse f 6
  have hforward : dot f (adjacency f) = 2 * (q 0 + q 2 + q 4 + q 6) := by
    rw [hsum, Fin.sum_univ_eight, h10, h32, h54, h76]
    ring
  rw [hforward]
  congr 1
  have h0 : q 0 = ∑ x : Fin n, ∑ y : Fin n,
      g x y * g ⟨(x.val + 2 * y.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩ y := by
    simp only [q, sum_reindex n]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [step_zero_fin]
  have h2 : q 2 = ∑ x : Fin n, ∑ y : Fin n,
      g x y * g ⟨(x.val + 2 * y.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ y := by
    simp only [q, sum_reindex n]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [step_two_fin]
  have h4 : q 4 = ∑ x : Fin n, ∑ y : Fin n,
      g x y * g x ⟨(2 * x.val + y.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := by
    simp only [q, sum_reindex n]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [step_four_fin]
  have h6 : q 6 = ∑ x : Fin n, ∑ y : Fin n,
      g x y * g x ⟨(2 * x.val + y.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := by
    simp only [q, sum_reindex n]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [step_six_fin]
  rw [h0, h2, h4, h6]
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

private theorem adjacency_dft_bridge (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (f : Vertex n → ℝ) :
    let g : Fin n → Fin n → ℝ :=
      fun x y => f ((x.val : ZMod n), (y.val : ZMod n))
    let G : Fin n → Fin n → ℝ := fun α₁ α₂ => ‖dft2d n g α₁ α₂‖
    |dot f (adjacency f)| * ((↑n : ℝ) ^ 2 / 4) ≤
      ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        G α₁ α₂ * (G (shearS2Fin n (by omega) (α₁, α₂)).1
                      (shearS2Fin n (by omega) (α₁, α₂)).2 *
                    |cos (↑π * ↑α₁.val / ↑n)| +
                    G (shearS1Fin n (by omega) (α₁, α₂)).1
                      (shearS1Fin n (by omega) (α₁, α₂)).2 *
                    |cos (↑π * ↑α₂.val / ↑n)|) := by
  intro g G
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn0 : 0 < n := by omega
  -- Abbreviate the correlation sums
  set C₁ := ∑ x : Fin n, ∑ y : Fin n,
    g x y * (g ⟨(x.val + 2 * y.val) % n, Nat.mod_lt _ hn0⟩ y +
             g ⟨(x.val + 2 * y.val + 1) % n, Nat.mod_lt _ hn0⟩ y)
  set C₂ := ∑ x : Fin n, ∑ y : Fin n,
    g x y * (g x ⟨(2 * x.val + y.val) % n, Nat.mod_lt _ hn0⟩ +
             g x ⟨(2 * x.val + y.val + 1) % n, Nat.mod_lt _ hn0⟩)
  -- Step 1: Walk operator expansion: 4*inner = C₁ + C₂
  have hcorr := dot_adjacency_eq_correlations n f
  -- Step 2: DFT of correlation sums (from corr_pair1/2, complex-valued)
  have hF₁ := corr_pair1 n (by omega) g hn
  have hF₂ := corr_pair2 n (by omega) g hn
  -- Abbreviate the Fourier sums
  set F₁ := ∑ α₁ : Fin n, ∑ α₂ : Fin n,
    dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g α₁
      ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn0⟩) *
    (1 + ω n ^ (-(α₁.val : ℤ)))
  set F₂ := ∑ α₁ : Fin n, ∑ α₂ : Fin n,
    dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g
      ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ hn0⟩ α₂) *
    (1 + ω n ^ (-(α₂.val : ℤ)))
  -- hF₁ : (↑n)² * ↑C₁ = F₁, hF₂ : (↑n)² * ↑C₂ = F₂
  -- Step 3: |inner| * 2n² = |C₁+C₂|/4 * 2n² = |C₁+C₂| * n²/2
  -- From hcorr: 4*inner = C₁+C₂ → inner = (C₁+C₂)/4
  have h_inner : dot f (adjacency f) = 2 * (C₁ + C₂) := by
    simpa only using hcorr
  rw [h_inner, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h4 : 2 * |C₁ + C₂| * ((↑n : ℝ) ^ 2 / 4) =
      |C₁ + C₂| * (↑n : ℝ) ^ 2 / 2 := by ring
  rw [h4]
  -- Now bound |C₁+C₂| * n²/2
  -- n²*C₁ = Re(F₁) in ℝ: extract from the complex equality
  have h_re_cast : ((↑n : ℂ) ^ 2).re = (↑n : ℝ) ^ 2 := by norm_cast
  have h_C₁_re : (↑n : ℝ) ^ 2 * C₁ = (F₁).re := by
    have := congr_arg Complex.re hF₁
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at this
    rw [h_re_cast] at this; exact this
  have h_C₂_re : (↑n : ℝ) ^ 2 * C₂ = (F₂).re := by
    have := congr_arg Complex.re hF₂
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at this
    rw [h_re_cast] at this; exact this
  -- |C₁+C₂|*n²/2 = |n²*C₁ + n²*C₂|/2 = |Re(F₁) + Re(F₂)|/2
  have h_sum : |C₁ + C₂| * (↑n : ℝ) ^ 2 = |F₁.re + F₂.re| := by
    have h_nn : (0 : ℝ) ≤ (↑n : ℝ) ^ 2 := by positivity
    rw [mul_comm, ← abs_of_nonneg h_nn, ← abs_mul, mul_add, h_C₁_re, h_C₂_re]
  rw [h_sum]
  -- |Re(F₁) + Re(F₂)|/2 ≤ (‖F₁‖ + ‖F₂‖)/2  [|Re z| ≤ ‖z‖]
  -- ≤ (∑|term₁| + ∑|term₂|)/2  [triangle inequality on sums]
  -- Each |term| = G*G∘S*‖1+ω‖ = G*G∘S*2|cos|  [norm_one_add_ω_inv]
  -- So ≤ (2*∑G*G∘S₂*|cos₁| + 2*∑G*G∘S₁*|cos₂|)/2
  -- = ∑G*(G∘S₂*|cos₁| + G∘S₁*|cos₂|)
  -- Bound |Re(F₁)+Re(F₂)| ≤ |Re(F₁)| + |Re(F₂)| ≤ ‖F₁‖ + ‖F₂‖
  have hre_le : |F₁.re + F₂.re| / 2 ≤ (‖F₁‖ + ‖F₂‖) / 2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) < 2).le
    calc |F₁.re + F₂.re| ≤ |F₁.re| + |F₂.re| := abs_add_le _ _
      _ ≤ ‖F₁‖ + ‖F₂‖ := add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
  -- Bound ‖F_j‖ ≤ ∑‖term_j‖ (triangle inequality on sums)
  have hF₁_tri : ‖F₁‖ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ * G α₁ ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn0⟩ *
      ‖(1 : ℂ) + ω n ^ (-(α₁.val : ℤ))‖ := by
    calc ‖F₁‖ ≤ ∑ α₁ : Fin n, ‖∑ α₂ : Fin n,
        dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g α₁
          ⟨(α₂.val + n - (2 * α₁.val) % n) % n, _⟩) *
        (1 + ω n ^ (-(α₁.val : ℤ)))‖ := norm_sum_le _ _
      _ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        ‖dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g α₁
          ⟨(α₂.val + n - (2 * α₁.val) % n) % n, _⟩) *
        (1 + ω n ^ (-(α₁.val : ℤ)))‖ := by
        gcongr with α₁; exact norm_sum_le _ _
      _ = _ := by
        congr 1; ext α₁; congr 1; ext α₂
        rw [norm_mul, norm_mul, Complex.norm_conj]
  have hF₂_tri : ‖F₂‖ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ * G ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ hn0⟩ α₂ *
      ‖(1 : ℂ) + ω n ^ (-(α₂.val : ℤ))‖ := by
    calc ‖F₂‖ ≤ ∑ α₁ : Fin n, ‖∑ α₂ : Fin n,
        dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g
          ⟨(α₁.val + n - (2 * α₂.val) % n) % n, _⟩ α₂) *
        (1 + ω n ^ (-(α₂.val : ℤ)))‖ := norm_sum_le _ _
      _ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        ‖dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g
          ⟨(α₁.val + n - (2 * α₂.val) % n) % n, _⟩ α₂) *
        (1 + ω n ^ (-(α₂.val : ℤ)))‖ := by
        gcongr with α₁; exact norm_sum_le _ _
      _ = _ := by
        congr 1; ext α₁; congr 1; ext α₂
        rw [norm_mul, norm_mul, Complex.norm_conj]
  -- Apply norm_one_add_ω_inv: ‖1+ω^{-a}‖ = 2*|cos(πa/n)|
  simp_rw [norm_one_add_ω_inv n (by omega)] at hF₁_tri hF₂_tri
  -- Chain everything
  calc |F₁.re + F₂.re| / 2
      ≤ (‖F₁‖ + ‖F₂‖) / 2 := hre_le
    _ ≤ ((∑ α₁, ∑ α₂, G α₁ α₂ * G α₁ ⟨(α₂.val + n - (2 * α₁.val) % n) % n, _⟩ *
            (2 * |cos (↑π * ↑α₁.val / ↑n)|)) +
         (∑ α₁, ∑ α₂, G α₁ α₂ * G ⟨(α₁.val + n - (2 * α₂.val) % n) % n, _⟩ α₂ *
            (2 * |cos (↑π * ↑α₂.val / ↑n)|))) / 2 := by
        gcongr
    _ = ∑ α₁, ∑ α₂, G α₁ α₂ *
          (G (shearS2Fin n hn0 (α₁, α₂)).1 (shearS2Fin n hn0 (α₁, α₂)).2 *
            |cos (↑π * ↑α₁.val / ↑n)| +
           G (shearS1Fin n hn0 (α₁, α₂)).1 (shearS1Fin n hn0 (α₁, α₂)).2 *
            |cos (↑π * ↑α₂.val / ↑n)|) := by
      -- Factor out 2/2 = 1 and combine sums
      rw [div_eq_iff (show (2:ℝ) ≠ 0 by norm_num)]
      rw [← Finset.sum_add_distrib]
      simp_rw [← Finset.sum_add_distrib]
      conv_rhs => rw [Finset.sum_mul]; arg 2; ext; rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro α₁ _
      apply Finset.sum_congr rfl; intro α₂ _
      simp only [shearS2Fin, shearS1Fin]
      ring

/-- Sharp quadratic-form estimate for the actual eight labelled maps when `3 ≤ n`. -/
theorem adjacency_quadratic_le (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (f : Vertex n → ℝ) (hf : f ∈ MeanZero) :
    |dot f (adjacency f)| ≤ 5 * √2 * energy f := by
  let g : Fin n → Fin n → ℝ :=
    fun x y => f ((x.val : ZMod n), (y.val : ZMod n))
  let G : Fin n → Fin n → ℝ := fun a b => ‖dft2d n g a b‖
  have hsum_g : ∑ x, ∑ y, g x y = 0 := by
    rw [← sum_reindex n]
    exact hf
  have hG0 : G ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by
    rw [show G ⟨0, by omega⟩ ⟨0, by omega⟩ =
      ‖dft2d n g ⟨0, by omega⟩ ⟨0, by omega⟩‖ from rfl]
    rw [norm_eq_zero, dft2d_zero n g (by omega)]
    exact_mod_cast hsum_g
  have hchain : |dot f (adjacency f)| * ((n : ℝ) ^ 2 / 4) ≤
      5 * √2 / 4 * ∑ a, ∑ b, G a b ^ 2 :=
    (adjacency_dft_bridge n hn f).trans (young_assembly n hn G hG0)
  have hG2 : ∑ a, ∑ b, G a b ^ 2 =
      ∑ a, ∑ b, Complex.normSq (dft2d n g a b) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact Complex.sq_norm _
  have hg_energy : ∑ x, ∑ y, g x y ^ 2 = energy f := by
    change (∑ x : Fin n, ∑ y : Fin n,
      f ((x.val : ZMod n), (y.val : ZMod n)) ^ 2) =
      ∑ v, f v ^ 2
    exact (sum_reindex n (fun v => f v ^ 2)).symm
  rw [hG2, parseval_2d n (by omega) g, hg_energy] at hchain
  have hfactor : 0 < (n : ℝ) ^ 2 / 4 := by positivity
  have hrearrange : 5 * √2 / 4 * ((n : ℝ) ^ 2 * energy f) =
      (5 * √2 * energy f) * ((n : ℝ) ^ 2 / 4) := by ring
  rw [hrearrange] at hchain
  exact le_of_mul_le_mul_right hchain hfactor

private theorem dot_add_left {n : ℕ} [NeZero n]
    (f g h : Vertex n → ℝ) : dot (f + g) h = dot f h + dot g h := by
  simp [dot, add_mul, Finset.sum_add_distrib]

private theorem dot_add_right {n : ℕ} [NeZero n]
    (f g h : Vertex n → ℝ) : dot f (g + h) = dot f g + dot f h := by
  simp [dot, mul_add, Finset.sum_add_distrib]

private theorem dot_smul_left {n : ℕ} [NeZero n]
    (c : ℝ) (f g : Vertex n → ℝ) : dot (c • f) g = c * dot f g := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ v, c * f v * g v) = ∑ v, c * (f v * g v) := by
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = c * ∑ v, f v * g v := (Finset.mul_sum ..).symm

private theorem dot_smul_right {n : ℕ} [NeZero n]
    (c : ℝ) (f g : Vertex n → ℝ) : dot f (c • g) = c * dot f g := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ v, f v * (c * g v)) = ∑ v, c * (f v * g v) := by
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = c * ∑ v, f v * g v := (Finset.mul_sum ..).symm

private theorem dot_self_eq_energy {n : ℕ} [NeZero n] (f : Vertex n → ℝ) :
    dot f f = energy f := by
  unfold dot energy
  apply Finset.sum_congr rfl
  intro v _
  ring

private theorem energy_add_sub {n : ℕ} [NeZero n]
    (c : ℝ) (f g : Vertex n → ℝ) :
    energy (f + c • g) + energy (f - c • g) =
      2 * energy f + 2 * c ^ 2 * energy g := by
  unfold energy
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  simp_rw [show ∀ v, (f v + c * g v) ^ 2 + (f v - c * g v) ^ 2 =
    2 * f v ^ 2 + 2 * c ^ 2 * g v ^ 2 by intro v; ring]
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The sharp quadratic bound implies the squared-energy estimate by self-adjoint polarization. -/
theorem adjacency_energy_le (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (f : Vertex n → ℝ) (hf : f ∈ MeanZero) :
    energy (adjacency f) ≤ 50 * energy f := by
  let c : ℝ := 5 * √2
  let a := adjacency f
  have ha : a ∈ MeanZero := adjacency_mem_meanZero hf
  have hp_mem : a + c • f ∈ MeanZero :=
    Submodule.add_mem _ ha (Submodule.smul_mem _ c hf)
  have hm_mem : a - c • f ∈ MeanZero :=
    Submodule.sub_mem _ ha (Submodule.smul_mem _ c hf)
  have hp := adjacency_quadratic_le n hn (a + c • f) hp_mem
  have hm := adjacency_quadratic_le n hn (a - c • f) hm_mem
  have hp' : dot (a + c • f) (adjacency (a + c • f)) ≤
      c * energy (a + c • f) := by
    exact (le_abs_self _).trans hp
  have hm' : -dot (a - c • f) (adjacency (a - c • f)) ≤
      c * energy (a - c • f) := by
    exact (neg_le_abs _).trans hm
  have hself : dot f (adjacency a) = energy a := by
    rw [← dot_self_eq_energy]
    exact (adjacency_selfAdjoint f a).symm
  have hpolar :
      dot (a + c • f) (adjacency (a + c • f)) -
        dot (a - c • f) (adjacency (a - c • f)) = 4 * c * energy a := by
    rw [adjacency_add, adjacency_smul]
    simp only [sub_eq_add_neg, ← neg_smul, adjacency_add, adjacency_smul,
      dot_add_left, dot_add_right, dot_smul_left, dot_smul_right]
    rw [dot_self_eq_energy, hself]
    ring
  have hdiff :
      dot (a + c • f) (adjacency (a + c • f)) -
        dot (a - c • f) (adjacency (a - c • f)) ≤
        c * (energy (a + c • f) + energy (a - c • f)) := by
    linarith
  rw [hpolar, energy_add_sub] at hdiff
  have hc : 0 < c := by dsimp [c]; positivity
  have hc_sq : c ^ 2 = 50 := by
    dsimp [c]
    rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have ha_nonneg := energy_nonneg a
  change energy a ≤ 50 * energy f
  rw [hc_sq] at hdiff
  nlinarith

private theorem exactEnergyEstimate_one : ExactEnergyEstimate 1 := by
  intro f hf
  have h0 : f (0, 0) = 0 := by
    rw [mem_meanZero_iff, sum_reindex 1] at hf
    simp only [Fin.sum_univ_one] at hf
    norm_num at hf ⊢
    exact hf
  have hf_zero : f = 0 := by
    funext v
    rcases v with ⟨x, y⟩
    fin_cases x
    fin_cases y
    exact h0
  rw [hf_zero]
  unfold energy
  simp

private theorem adjacency_two_apply (f : Vertex 2 → ℝ) (v : Vertex 2) :
    adjacency f v = 4 * f v + 2 * f (v.1 + 1, v.2) + 2 * f (v.1, v.2 + 1) := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hneg_one : (-1 : ZMod 2) = 1 := by decide
  rcases v with ⟨x, y⟩
  have hdouble (z : ZMod 2) : 2 * z = 0 := by rw [htwo, zero_mul]
  have hsub_one (z : ZMod 2) : z - 1 = z + 1 := by
    rw [sub_eq_add_neg, hneg_one]
  rw [adjacency_apply, Fin.sum_univ_eight]
  change
    f (x + 2 * y, y) + f (x - 2 * y, y) + f (x + (2 * y + 1), y) +
      f (x - (2 * y + 1), y) + f (x, y + 2 * x) + f (x, y - 2 * x) +
      f (x, y + (2 * x + 1)) + f (x, y - (2 * x + 1)) = _
  simp_rw [hdouble]
  simp only [add_zero, sub_zero, zero_add, hsub_one]
  ring

private theorem exactEnergyEstimate_two : ExactEnergyEstimate 2 := by
  intro f hf
  have hsum : f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1) = 0 := by
    rw [mem_meanZero_iff, sum_reindex 2] at hf
    simp only [Fin.sum_univ_two] at hf
    norm_num at hf ⊢
    linarith
  unfold energy
  rw [sum_reindex 2, sum_reindex 2]
  simp only [Fin.sum_univ_two]
  rw [adjacency_two_apply, adjacency_two_apply, adjacency_two_apply,
    adjacency_two_apply]
  have hsum_one : (1 + 1 : ZMod 2) = 0 := by decide
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.cast_zero, zero_add,
    Nat.mod_succ, Nat.cast_one, ge_iff_le, hsum_one]
  have h00 : 4 * f (0, 0) + 2 * f (1, 0) + 2 * f (0, 1) =
      2 * (f (0, 0) - f (1, 1)) := by linarith
  have h01 : 4 * f (0, 1) + 2 * f (1, 1) + 2 * f (0, 0) =
      2 * (f (0, 1) - f (1, 0)) := by linarith
  have h10 : 4 * f (1, 0) + 2 * f (0, 0) + 2 * f (1, 1) =
      2 * (f (1, 0) - f (0, 1)) := by linarith
  have h11 : 4 * f (1, 1) + 2 * f (0, 1) + 2 * f (1, 0) =
      2 * (f (1, 1) - f (0, 0)) := by linarith
  rw [h00, h01, h10, h11]
  nlinarith [sq_nonneg (f (0, 0) + f (1, 1)),
    sq_nonneg (f (0, 1) + f (1, 0)), sq_nonneg (f (0, 0)),
    sq_nonneg (f (0, 1)), sq_nonneg (f (1, 0)), sq_nonneg (f (1, 1))]

/-- The exact squared-energy estimate for every positive modulus, including composite moduli. -/
theorem exactEnergyEstimate (m : ℕ) [NeZero m] : ExactEnergyEstimate m := by
  by_cases hm : 3 ≤ m
  · intro f hf
    exact adjacency_energy_le m hm f hf
  · have hm_pos := NeZero.pos m
    interval_cases m
    · exact exactEnergyEstimate_one
    · exact exactEnergyEstimate_two


end GabberGalil.EnergyEstimate

namespace GabberGalil

/-- The Gabber--Galil squared-energy estimate for all positive side lengths. -/
theorem exactEnergyEstimate (m : ℕ) [NeZero m] : ExactEnergyEstimate m :=
  EnergyEstimate.exactEnergyEstimate m

end GabberGalil

end
