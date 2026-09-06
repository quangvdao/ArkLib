/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.HeightCounting
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveRank
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.Band


/-!
# Exact finite height sums for polynomial received curves

For a received curve of degree at most `ℓ`, a source monomial with `Y₀` exponent `a`
has challenge-column degree at most `ℓ * a`. Reindexing the full first-order support
by total jet degree `t` and first-derivative exponent `b` gives `a = t - b`.
The resulting executable sum counts every permitted scalar coefficient, including inactive
columns through natural-number truncated subtraction. The shifted construction below grades
both sides by total jet degree. A degree-`t` source column then has weight `ℓ*t`, while the
actual degree-`t` local image contributes `r_t` rows of that same weight.
-/

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

variable {D A m M μ ℓ h : ℕ}

/-- Total number of polynomial coefficient slots allowed by height `h` across the actual finite
first-order support. -/
def firstOrderCurveColumnSlotCount (D A m M μ ℓ h : ℕ) : ℕ :=
  Finset.sum (firstOrderExponents D A m M μ) fun u ↦ h + 1 - ℓ * u (some 0)

/-- Executable nested sum for the first-order column-height slot count. -/
def firstOrderCurveHeightSlotCount (D A m M μ ℓ h : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    Finset.sum (Finset.range (min t M + 1)) fun b ↦
      (m * A + b - D * t) * (h + 1 - ℓ * (t - b))

/-- The dependent `(t,b,x)` index has the expected weighted cardinality, where every `x` at a
fixed `(t,b)` contributes the same number of height slots. -/
theorem sum_firstOrderDimensionIndex_curveHeight (D A m M μ ℓ h : ℕ) :
    (Finset.univ.sum fun q : FirstOrderDimensionIndex D A m M μ ↦
        h + 1 - ℓ * (q.1.val - q.2.1.val)) =
      firstOrderCurveHeightSlotCount D A m M μ ℓ h := by
  rw [Fintype.sum_sigma]
  calc
    (Finset.univ.sum fun t : Fin (μ + 1) ↦
        Finset.univ.sum fun q : (Σ b : Fin (min t.val M + 1),
          Fin (m * A + b.val - D * t.val)) ↦
          h + 1 - ℓ * (t.val - q.1.val)) =
        Finset.univ.sum fun t : Fin (μ + 1) ↦
          Finset.univ.sum fun b : Fin (min t.val M + 1) ↦
            (m * A + b.val - D * t.val) * (h + 1 - ℓ * (t.val - b.val)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro b _
      simp
    _ = Finset.sum (Finset.range (μ + 1)) fun t ↦
          Finset.univ.sum fun b : Fin (min t M + 1) ↦
            (m * A + b.val - D * t) * (h + 1 - ℓ * (t - b.val)) := by
      exact Fin.sum_univ_eq_sum_range
        (fun t ↦ Finset.univ.sum fun b : Fin (min t M + 1) ↦
          (m * A + b.val - D * t) * (h + 1 - ℓ * (t - b.val))) (μ + 1)
    _ = Finset.sum (Finset.range (μ + 1)) fun t ↦
          Finset.sum (Finset.range (min t M + 1)) fun b ↦
            (m * A + b - D * t) * (h + 1 - ℓ * (t - b)) := by
      apply Finset.sum_congr rfl
      intro t _
      exact Fin.sum_univ_eq_sum_range
        (fun b ↦ (m * A + b - D * t) * (h + 1 - ℓ * (t - b))) (min t M + 1)
    _ = firstOrderCurveHeightSlotCount D A m M μ ℓ h := rfl

/-- The support-side column-slot sum is exactly the executable nested height sum. -/
theorem firstOrderCurveColumnSlotCount_eq_heightSlotCount (hD : 0 < D) :
    firstOrderCurveColumnSlotCount D A m M μ ℓ h =
      firstOrderCurveHeightSlotCount D A m M μ ℓ h := by
  rw [firstOrderCurveColumnSlotCount, ← Finset.sum_attach]
  let e := firstOrderExponentDimensionIndexEquiv
    (D := D) (A := A) (m := m) (M := M) (μ := μ) hD
  calc
    (Finset.univ.sum fun u : ↑(firstOrderExponents D A m M μ) ↦
        h + 1 - ℓ * u.1 (some 0)) =
        Finset.univ.sum fun q : FirstOrderDimensionIndex D A m M μ ↦
          h + 1 - ℓ * (q.1.val - q.2.1.val) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro u _
      rw [firstOrderExponentDimensionIndex_y₀ hD]
    _ = firstOrderCurveHeightSlotCount D A m M μ ℓ h :=
      sum_firstOrderDimensionIndex_curveHeight D A m M μ ℓ h

/-! ### Shifted source and row profiles -/

/-- Under the support equivalence, the source total jet degree is the outer index `t`. -/
theorem firstOrderExponentDimensionIndex_totalJetDegree (hD : 0 < D)
    (u : ↑(firstOrderExponents D A m M μ)) :
    totalJetDegree u.1 = (firstOrderExponentDimensionIndexEquiv hD u).1.val := by
  let hd : 0 < 1 := by omega
  change totalJetDegree u.1 =
    (exactExponentCoordinatesEquiv hd u.1).2.1.1 +
      (exactExponentCoordinatesEquiv hd u.1).2.1.2
  simp only [totalJetDegree, Finsupp.degree_eq_sum,
    exactExponentCoordinatesEquiv_y₀, Finsupp.some_apply]
  rw [Fin.sum_univ_two]
  simp [exactExponentCoordinatesEquiv_y₁]

/-- Truncated source slots when a degree-`t` column receives challenge weight `ℓ*t`. -/
def firstOrderCurveShiftedColumnSlotCount (D A m M μ ℓ h : ℕ) : ℕ :=
  Finset.sum (firstOrderExponents D A m M μ) fun u ↦
    h + 1 - ℓ * totalJetDegree u

/-- Executable nested form of the shifted source-slot count. -/
def firstOrderCurveShiftedHeightSlotCount (D A m M μ ℓ h : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    Finset.sum (Finset.range (min t M + 1)) fun b ↦
      (m * A + b - D * t) * (h + 1 - ℓ * t)

/-- Reindexing by `(t,b,x)` turns the shifted source count into its executable nested sum. -/
theorem firstOrderCurveShiftedColumnSlotCount_eq_heightSlotCount (hD : 0 < D) :
    firstOrderCurveShiftedColumnSlotCount D A m M μ ℓ h =
      firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h := by
  rw [firstOrderCurveShiftedColumnSlotCount, ← Finset.sum_attach]
  let e := firstOrderExponentDimensionIndexEquiv
    (D := D) (A := A) (m := m) (M := M) (μ := μ) hD
  calc
    Finset.univ.sum (fun u : ↑(firstOrderExponents D A m M μ) ↦
        h + 1 - ℓ * totalJetDegree u.1) =
        Finset.univ.sum (fun q : FirstOrderDimensionIndex D A m M μ ↦
          h + 1 - ℓ * q.1.val) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro u _
      rw [firstOrderExponentDimensionIndex_totalJetDegree hD]
    _ = firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h := by
      rw [Fintype.sum_sigma]
      calc
        (Finset.univ.sum fun t : Fin (μ + 1) ↦
            Finset.univ.sum fun q : (Σ b : Fin (min t.val M + 1),
              Fin (m * A + b.val - D * t.val)) ↦ h + 1 - ℓ * t.val) =
            Finset.univ.sum fun t : Fin (μ + 1) ↦
              Finset.univ.sum fun b : Fin (min t.val M + 1) ↦
                (m * A + b.val - D * t.val) * (h + 1 - ℓ * t.val) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro b _
          simp
        _ = Finset.sum (Finset.range (μ + 1)) fun t ↦
              Finset.univ.sum fun b : Fin (min t M + 1) ↦
                (m * A + b.val - D * t) * (h + 1 - ℓ * t) := by
          exact Fin.sum_univ_eq_sum_range
            (fun t ↦ Finset.univ.sum fun b : Fin (min t M + 1) ↦
              (m * A + b.val - D * t) * (h + 1 - ℓ * t)) (μ + 1)
        _ = Finset.sum (Finset.range (μ + 1)) fun t ↦
              Finset.sum (Finset.range (min t M + 1)) fun b ↦
                (m * A + b - D * t) * (h + 1 - ℓ * t) := by
          apply Finset.sum_congr rfl
          intro t _
          exact Fin.sum_univ_eq_sum_range
            (fun b ↦ (m * A + b - D * t) * (h + 1 - ℓ * t)) (min t M + 1)
        _ = firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h := rfl

/-- Truncated row slots supplied by the actual base-field graded images at `n` points. -/
def firstOrderCurveShiftedRowSlotCount (F : Type*) [Field F]
    (D A m M μ n ℓ h : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    n * firstOrderGradedRank F D A m M t * (h + 1 - ℓ * t)

/-- Executable upper bound on shifted row slots obtained from the sharp numerical block
profile. -/
def firstOrderCurveShiftedRowSlotBound
    (D A m M μ n ℓ h : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    n * firstOrderGradedRankBound D A m M t * (h + 1 - ℓ * t)

/-- The actual compressed-row slot count is bounded by the sharp paper profile. -/
theorem firstOrderCurveShiftedRowSlotCount_le_bound
    {F : Type*} [Field F] (D A m M μ n ℓ h : ℕ) :
    firstOrderCurveShiftedRowSlotCount F D A m M μ n ℓ h ≤
      firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h := by
  apply Finset.sum_le_sum
  intro t ht
  exact Nat.mul_le_mul_right (h + 1 - ℓ * t)
    (Nat.mul_le_mul_left n (firstOrderOriginGradedRank_le_bound (F := F) D A m M t))

/-- The finite type of fixed compressed rows has exactly the truncated weighted slot count. -/
theorem sum_firstOrderCurveGradedRowIndex_slots
    {F : Type*} [Field F] (D A m M μ n ℓ h : ℕ) :
    (Finset.univ.sum fun row : FirstOrderCurveGradedRowIndex F D A m M μ n ↦
      h + 1 - ℓ * row.2.1.val) =
      firstOrderCurveShiftedRowSlotCount F D A m M μ n ℓ h := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  rw [firstOrderCurveShiftedRowSlotCount, ← Fin.sum_univ_eq_sum_range]
  simp_rw [Nat.mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  simp only [firstOrderGradedRank, firstOrderOriginGradedRank]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  simp

/-- Flattening the compressed row index preserves its exact truncated weighted slot count. -/
theorem sum_firstOrderCurveGradedFinRowWeight_slots
    {F : Type*} [Field F] (D A m M μ n ℓ h : ℕ) :
    (Finset.univ.sum fun i :
        Fin (Fintype.card (FirstOrderCurveGradedRowIndex F D A m M μ n)) ↦
      h + 1 - firstOrderCurveGradedFinRowWeight F D A m M μ n ℓ i) =
      firstOrderCurveShiftedRowSlotCount F D A m M μ n ℓ h := by
  rw [← Equiv.sum_comp
    (Fintype.equivFin (FirstOrderCurveGradedRowIndex F D A m M μ n))]
  simpa [firstOrderCurveGradedFinRowWeight, firstOrderCurveGradedRowWeight] using
    (sum_firstOrderCurveGradedRowIndex_slots (F := F) D A m M μ n ℓ h)

/-- The exact truncated shifted-height test. -/
def FirstOrderCurveShiftedHeightSurplus (F : Type*) [Field F]
    (D A m M μ n ℓ h : ℕ) : Prop :=
  firstOrderCurveShiftedRowSlotCount F D A m M μ n ℓ h <
    firstOrderCurveShiftedColumnSlotCount D A m M μ ℓ h

/-- Total source weight, used to simplify the shifted test when every source block is active. -/
def firstOrderTotalJetWeight (D A m M μ : ℕ) : ℕ :=
  Finset.sum (firstOrderExponents D A m M μ) totalJetDegree

/-- Total row weight of the actual graded image at one point. -/
def firstOrderGradedRowWeight (F : Type*) [Field F]
    (D A m M μ : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    firstOrderGradedRank F D A m M t * t

/-- In the all-active range, the source slots equal a rectangle minus the weighted profile. -/
theorem firstOrderCurveShiftedColumnSlotCount_add_weight
    (hactive : ℓ * μ ≤ h) :
    firstOrderCurveShiftedColumnSlotCount D A m M μ ℓ h +
        ℓ * firstOrderTotalJetWeight D A m M μ =
      (firstOrderExponents D A m M μ).card * (h + 1) := by
  rw [firstOrderCurveShiftedColumnSlotCount, firstOrderTotalJetWeight,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    Finset.sum (firstOrderExponents D A m M μ)
        (fun u ↦ h + 1 - ℓ * totalJetDegree u + ℓ * totalJetDegree u) =
        Finset.sum (firstOrderExponents D A m M μ) (fun _ ↦ h + 1) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Nat.sub_add_cancel]
      have hut : totalJetDegree u ≤ μ :=
        (mem_firstOrderExponents.mp hu).2.1
      exact (Nat.mul_le_mul_left ℓ hut).trans (hactive.trans (Nat.le_add_right h 1))
    _ = (firstOrderExponents D A m M μ).card * (h + 1) := by simp

/-- In the all-active range, compressed row slots also equal a rectangle minus the weighted
actual-rank profile. -/
theorem firstOrderCurveShiftedRowSlotCount_add_weight
    {F : Type*} [Field F] {n : ℕ} (hactive : ℓ * μ ≤ h) :
    firstOrderCurveShiftedRowSlotCount F D A m M μ n ℓ h +
        n * ℓ * firstOrderGradedRowWeight F D A m M μ =
      n * (∑ t ∈ Finset.range (μ + 1), firstOrderGradedRank F D A m M t) *
        (h + 1) := by
  rw [firstOrderCurveShiftedRowSlotCount, firstOrderGradedRowWeight,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    (∑ t ∈ Finset.range (μ + 1),
        (n * firstOrderGradedRank F D A m M t * (h + 1 - ℓ * t) +
          n * ℓ * (firstOrderGradedRank F D A m M t * t))) =
        (∑ t ∈ Finset.range (μ + 1),
          n * firstOrderGradedRank F D A m M t * (h + 1)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htμ : t ≤ μ := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp ht)
      have hweight : ℓ * t ≤ h + 1 :=
        (Nat.mul_le_mul_left ℓ htμ).trans (hactive.trans (Nat.le_add_right h 1))
      rw [show n * ℓ * (firstOrderGradedRank F D A m M t * t) =
          n * firstOrderGradedRank F D A m M t * (ℓ * t) by ring]
      rw [← Nat.mul_add, Nat.sub_add_cancel hweight]
    _ = (∑ t ∈ Finset.range (μ + 1),
        n * firstOrderGradedRank F D A m M t) * (h + 1) := by
      rw [Finset.sum_mul]


end

end ReedSolomon.HiddenDerivative
