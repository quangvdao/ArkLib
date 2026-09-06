/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Interpolation
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.HeightCounting
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.SymbolicRank
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.GradedRank
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve

/-!
# First-order rank bounds for polynomial received curves

The first-order constraint-rank theorem holds over every field. At the origin, the local map
splits into homogeneous blocks indexed by total jet degree, counting the error variable `E` as
degree one. This file defines each profile entry as the dimension of the actual block image.
Thus the profile records upper bounds coming from the constraint map itself; it does not assert
that a preselected numerical budget equals a rank.

Applying the aggregate theorem over `F(Z)` still controls polynomial received curves. The
received polynomials may have any degree: batching degree affects coefficient heights, while
the base-field graded images determine how many projected rows are needed at each degree.
-/

open PolynomialDifferential Polynomial
open scoped BigOperators Matrix

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicReceivedCurve SymbolicBandInterpolation

noncomputable section

variable {F : Type*} [Field F]

/-! ### Translation stability of the finite first-order source -/

private def firstOrderFirstJetWeight : JetVariable 1 → ℕ
  | none => 0
  | some j => if j.val = 1 then 1 else 0

private theorem weight_firstOrderFirstJetWeight (u : JetVariable 1 →₀ ℕ) :
    Finsupp.weight firstOrderFirstJetWeight u = firstJetExponent u := by
  simp [firstOrderFirstJetWeight, firstJetExponent, Finsupp.weight_eq_sum,
    Fintype.sum_option]

/-- Translation in `X,Y₀` preserves all three defining bounds of the finite first-order
support: the `Y₁` cap, total jet-degree cap, and exact specialization-degree cutoff. -/
theorem globalPointTranslation_mem_firstOrderSpace
    (D A m M μ : ℕ) (center received : F) {Q : DifferentialPolynomial F 1}
    (hQ : Q ∈ firstOrderSpace F D A m M μ) :
    globalPointTranslation center received Q ∈ firstOrderSpace F D A m M μ := by
  rw [mem_firstOrderSpace_iff] at hQ ⊢
  intro e he
  have hfirst := globalPointTranslation_support_weight_le firstOrderFirstJetWeight
    (by simp [firstOrderFirstJetWeight]) (by simp [firstOrderFirstJetWeight])
    center received (a := M) (fun u hu => by
      rw [weight_firstOrderFirstJetWeight]
      exact (mem_firstOrderExponents.mp (hQ u hu)).1) he
  have htotal := totalJetDegree_le_of_mem_globalPointTranslation_support
    center received (t := μ) (fun u hu => (mem_firstOrderExponents.mp (hQ u hu)).2.1) he
  have hQne : Q ≠ 0 := by
    intro hzero
    simp [hzero] at he
  obtain ⟨u, hu⟩ := MvPolynomial.support_nonempty.mpr hQne
  have hbudget : 0 < m * A :=
    (Nat.zero_le (exactInterpolationMonomialWeight D u)).trans_lt
      (mem_firstOrderExponents.mp (hQ u hu)).2.2
  have hdegree := globalPointTranslation_support_weight_le (differentialWeight D)
    (by simp [differentialWeight]) (by simp [differentialWeight]) center received
    (a := m * A - 1) (fun u hu => by
      change exactInterpolationMonomialWeight D u ≤ m * A - 1
      have hu' := (mem_firstOrderExponents.mp (hQ u hu)).2.2
      omega) he
  rw [weight_firstOrderFirstJetWeight] at hfirst
  change exactInterpolationMonomialWeight D e ≤ m * A - 1 at hdegree
  rw [mem_firstOrderExponents]
  exact ⟨hfirst, htotal, by omega⟩

/-! ### Exact origin slice matrices -/

/-- Number of first-order source monomials of total jet degree `t` whose origin image has
`T`-degree `s`.  The source exponent `a` ranges from `t-M` through `min t s`; the whole slice
is inactive when its common specialization cost misses the strict cutoff. -/
def firstOrderGradedSourceCount (D A m M s t : ℕ) : ℕ :=
  if s + (D - 1) * t < m * A then min t s + 1 - (t - M) else 0

/-- The numerical block-rank profile from the paper: each `(s,t)` block is bounded by the
smaller of its source count and its `m-s` low-contact target coordinates. -/
def firstOrderGradedRankBound (D A m M t : ℕ) : ℕ :=
  ∑ s ∈ Finset.range m, min (m - s) (firstOrderGradedSourceCount D A m M s t)

/-- Canonical source column for the `q`-th monomial in the `(s,t)` origin slice. -/
def firstOrderGradedSourceColumn (D A m M s t : ℕ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) : SourceColumn 1 :=
  let a := t - M + q.val
  { x := s - a
    y₀ := a
    higher := fun _ ↦ t - a }

@[simp] theorem firstOrderGradedSourceColumn_x (D A m M s t : ℕ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) :
    (firstOrderGradedSourceColumn D A m M s t q).x = s - (t - M + q.val) := rfl

@[simp] theorem firstOrderGradedSourceColumn_y₀ (D A m M s t : ℕ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) :
    (firstOrderGradedSourceColumn D A m M s t q).y₀ = t - M + q.val := rfl

@[simp] theorem firstOrderGradedSourceColumn_higher (D A m M s t : ℕ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) (j : Fin 1) :
    (firstOrderGradedSourceColumn D A m M s t q).higher j = t - (t - M + q.val) := rfl

/-- An inhabited source slice is active and its encoded `Y₀` exponent lies in the paper's
interval `t-M ≤ a ≤ min t s`. -/
theorem firstOrderGradedSourceColumn_bounds (D A m M s t : ℕ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) :
    s + (D - 1) * t < m * A ∧
      t - M ≤ (firstOrderGradedSourceColumn D A m M s t q).y₀ ∧
      (firstOrderGradedSourceColumn D A m M s t q).y₀ ≤ min t s := by
  have hq := q.isLt
  simp only [firstOrderGradedSourceCount] at hq
  split at hq
  next hactive =>
    change s + (D - 1) * t < m * A ∧ t - M ≤ t - M + q.val ∧
      t - M + q.val ≤ min t s
    omega
  next hinactive => simp at hq

/-- Every canonical slice column has total jet degree `t`. -/
theorem firstOrderGradedSourceColumn_totalJetDegree (D A m M s t : ℕ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) :
    totalJetDegree (firstOrderGradedSourceColumn D A m M s t q).exponent = t := by
  have hbounds := firstOrderGradedSourceColumn_bounds D A m M s t q
  simp only [firstOrderGradedSourceColumn_y₀] at hbounds
  rw [SourceColumn.totalJetDegree_exponent]
  simp only [firstOrderGradedSourceColumn_y₀, firstOrderGradedSourceColumn_higher]
  rw [Fin.sum_univ_one]
  omega

/-- For positive `D`, every canonical slice column belongs to the uncapped first-order support;
the separate hypothesis `t ≤ μ` inserts it into the chosen finite support. -/
theorem firstOrderGradedSourceColumn_mem {D A m M s t μ : ℕ}
    (hD : 0 < D) (ht : t ≤ μ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) :
    (firstOrderGradedSourceColumn D A m M s t q).exponent ∈
      firstOrderExponents D A m M μ := by
  have hbounds := firstOrderGradedSourceColumn_bounds D A m M s t q
  simp only [firstOrderGradedSourceColumn_y₀] at hbounds
  rw [mem_firstOrderExponents_iff_coordinates]
  simp only [exactExponentCoordinatesEquiv_y₀, exactExponentCoordinatesEquiv_y₁,
    exactExponentCoordinatesEquiv_x, SourceColumn.exponent_none]
  have hindex0 : (⟨0, by omega⟩ : Fin 2) = 0 := by ext; rfl
  have hindex1 : (⟨1, by omega⟩ : Fin 2) = (0 : Fin 1).succ := by ext; rfl
  rw [hindex0, hindex1, SourceColumn.exponent_zero, SourceColumn.exponent_succ]
  simp only [firstOrderGradedSourceColumn_y₀, firstOrderGradedSourceColumn_higher,
    firstOrderGradedSourceColumn_x]
  change t - (t - M + q.val) ≤ M ∧
    (t - M + q.val) + (t - (t - M + q.val)) ≤ μ ∧
    (s - (t - M + q.val)) + D * (t - M + q.val) +
      (D - 1) * (t - (t - M + q.val)) < m * A
  let a := t - M + q.val
  have ha_t : a ≤ t := hbounds.2.2.trans (min_le_left _ _)
  have ha_s : a ≤ s := hbounds.2.2.trans (min_le_right _ _)
  have ht_split : a + (t - a) = t := Nat.add_sub_of_le ha_t
  have hs_split : s - a + a = s := Nat.sub_add_cancel ha_s
  have hDform : D - 1 + 1 = D := Nat.sub_add_cancel (by omega : 1 ≤ D)
  have hDa : D * a = (D - 1) * a + a := by
    calc
      D * a = (D - 1 + 1) * a := by rw [hDform]
      _ = _ := by rw [Nat.add_mul, one_mul]
  refine ⟨by omega, by omega, ?_⟩
  calc
    (s - a) + D * a + (D - 1) * (t - a) =
        (s - a + a) + (D - 1) * (a + (t - a)) := by
      rw [hDa]
      ring
    _ = s + (D - 1) * t := by rw [hs_split, ht_split]
    _ < m * A := hbounds.1

/-- The target exponent `T^s E^e Y₁^(t-e)` used by the literal `(s,t)` block matrix. -/
def firstOrderGradedTargetExponent (s t e : ℕ) : LocalVariable 1 →₀ ℕ :=
  Finsupp.single (localT 1) s + Finsupp.single (localE 1) e +
    Finsupp.single (localY (0 : Fin 1)) (t - e)

/-- A bounded target coordinate has local jet grade exactly `t`. -/
@[simp] theorem localJetDegree_firstOrderGradedTargetExponent
    {s t e : ℕ} (he : e ≤ t) :
    localJetDegree (firstOrderGradedTargetExponent s t e) = t := by
  simp [localJetDegree, localJetDegreeWeight, firstOrderGradedTargetExponent,
    Finsupp.weight_eq_sum, Fintype.sum_option, localT, localE, localAux, localY]
  omega

/-- Contact order of a literal first-order target coordinate. -/
@[simp] theorem localContactOrder_firstOrderGradedTargetExponent (s t e : ℕ) :
    localContactOrder 1 (firstOrderGradedTargetExponent s t e) = s + e := by
  simp [localContactOrder, localContactWeight, firstOrderGradedTargetExponent,
    Finsupp.weight_eq_sum, Fintype.sum_option, localT, localE, localAux, localY]

/-- The literal target coordinate as a certified low-contact row. -/
def firstOrderGradedTargetLowContactIndex {m : ℕ} (s : Fin m) (t : ℕ)
    (e : Fin (min (m - s.val) (t + 1))) : LowContactIndex 1 m :=
  ⟨firstOrderGradedTargetExponent s t e, by
    rw [localContactOrder_firstOrderGradedTargetExponent]
    have he : e.val < m - s.val := e.isLt.trans_le (min_le_left _ _)
    omega⟩

@[simp] theorem localJetDegree_firstOrderGradedTargetLowContactIndex
    {m : ℕ} (s : Fin m) (t : ℕ) (e : Fin (min (m - s.val) (t + 1))) :
    localJetDegree (firstOrderGradedTargetLowContactIndex s t e).1 = t := by
  apply localJetDegree_firstOrderGradedTargetExponent
  have := e.isLt.trans_le (min_le_right (m - s.val) (t + 1))
  omega

/-- Actual base-field origin constraint matrix on one fixed displacement/jet-grade block.
Its rows are literal local coefficients, and its columns are the exact admissible source slice. -/
def firstOrderOriginGradedSliceMatrix (D A m M s t : ℕ) :
    Matrix (Fin (min (m - s) (t + 1))) (Fin (firstOrderGradedSourceCount D A m M s t)) F :=
  fun e q ↦ MvPolynomial.coeff (firstOrderGradedTargetExponent s t e)
    (localConstraintAt m 0 0 (firstOrderGradedSourceColumn D A m M s t q).polynomial)

/-- Actual rank of the complete grade-`t` origin image, recorded as the sum of its disjoint
`T`-degree slice ranks. -/
noncomputable def firstOrderOriginGradedRank (F : Type*) [Field F]
    (D A m M t : ℕ) : ℕ :=
  ∑ s ∈ Finset.range m, (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).rank

/-- Each actual origin slice rank is bounded by both the literal target-row count and the exact
source-column count. -/
theorem firstOrderOriginGradedSliceMatrix_rank_le (D A m M s t : ℕ) :
    (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).rank ≤
      min (m - s) (firstOrderGradedSourceCount D A m M s t) := by
  apply le_min
  · exact (Matrix.rank_le_card_height
      (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t)).trans
        (by simp)
  · simpa using
      (Matrix.rank_le_card_width (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t))

/-- Fixed literal output rows, chosen over the base field, that form a basis of one actual
origin block's row space. -/
noncomputable def firstOrderOriginGradedSelectedRow (F : Type*) [Field F]
    (D A m M s t : ℕ) :
    Fin (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).rank →
      Fin (min (m - s) (t + 1)) :=
  Classical.choose
    (Matrix.exists_rows_fin_rank (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t))

/-- The selected literal rows span every row of the actual origin block. -/
theorem firstOrderOriginGradedSelectedRow_span (D A m M s t : ℕ) :
    Submodule.span F (Set.range fun i ↦
      (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).row
        (firstOrderOriginGradedSelectedRow F D A m M s t i)) =
      Submodule.span F (Set.range
        (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).row) :=
  (Classical.choose_spec
    (Matrix.exists_rows_fin_rank
      (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t))).2

/-- One origin block compressed to exactly its actual rank many fixed coefficient rows. -/
noncomputable def firstOrderOriginGradedCompressedMatrix (F : Type*) [Field F]
    (D A m M s t : ℕ) :
    Matrix (Fin (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).rank)
      (Fin (firstOrderGradedSourceCount D A m M s t)) F :=
  (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).submatrix
    (firstOrderOriginGradedSelectedRow F D A m M s t) id

/-- Compression keeps the full row space, hence keeps the kernel of the actual origin block. -/
theorem firstOrderOriginGradedCompressedMatrix_mulVec_eq_zero_iff
    (D A m M s t : ℕ)
    (v : Fin (firstOrderGradedSourceCount D A m M s t) → F) :
    (firstOrderOriginGradedCompressedMatrix F D A m M s t) *ᵥ v = 0 ↔
      (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t) *ᵥ v = 0 := by
  classical
  let A₀ := firstOrderOriginGradedSliceMatrix (F := F) D A m M s t
  let rows := firstOrderOriginGradedSelectedRow F D A m M s t
  constructor
  · intro hselected
    funext i
    change dotProduct (A₀.row i) v = 0
    have hi : A₀.row i ∈ Submodule.span F (Set.range fun j ↦ A₀.row (rows j)) := by
      rw [firstOrderOriginGradedSelectedRow_span (F := F) D A m M s t]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hzero_of_mem {x : Fin (firstOrderGradedSourceCount D A m M s t) → F}
        (hx : x ∈ Submodule.span F (Set.range fun j ↦ A₀.row (rows j))) :
        dotProduct x v = 0 := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨j, rfl⟩ := hx
          have hj := congrFun hselected j
          simpa [firstOrderOriginGradedCompressedMatrix, A₀, rows, Matrix.mulVec,
            dotProduct] using hj
      | zero => simp
      | add x y _ _ hx hy => simp [add_dotProduct, hx, hy]
      | smul a x _ hx => simp [smul_dotProduct, hx]
    exact hzero_of_mem hi
  · intro hall
    funext i
    have hi := congrFun hall (rows i)
    simpa [firstOrderOriginGradedCompressedMatrix, A₀, rows, Matrix.mulVec,
      dotProduct] using hi

/-! ### Fixed compressed rows for translated curve constraints -/

/-- Compressed rows at all points, jet grades, and displacement degrees. -/
abbrev FirstOrderCurveGradedRowIndex (F : Type*) [Field F]
    (D A m M μ n : ℕ) :=
  Fin n × Σ t : Fin (μ + 1), Σ s : Fin m,
    Fin (firstOrderOriginGradedSliceMatrix (F := F) D A m M s.val t.val).rank

/-- The literal low-contact coefficient selected by a compressed graded row. -/
noncomputable def firstOrderCurveGradedRowLocalIndex
    (F : Type*) [Field F] (D A m M μ n : ℕ)
    (row : FirstOrderCurveGradedRowIndex F D A m M μ n) : LowContactIndex 1 m :=
  firstOrderGradedTargetLowContactIndex row.2.2.1 row.2.1.val
    (firstOrderOriginGradedSelectedRow F D A m M row.2.2.1.val row.2.1.val row.2.2.2)

/-- The translated curve matrix on the fixed base-field compressed coefficient rows. -/
noncomputable def firstOrderCurveGradedConstraintMatrix
    (D A m M μ n : ℕ) (centers : Fin n → F) (w : Fin n → F[X]) :
    Matrix (FirstOrderCurveGradedRowIndex F D A m M μ n)
      (Fin (Fintype.card ↑(firstOrderExponents D A m M μ))) F[X] :=
  fun row j ↦
    constraintMatrix m centers w
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))
      (row.1, firstOrderCurveGradedRowLocalIndex F D A m M μ n row) j

/-- Reindex the compressed graded rows by a single `Fin` for the polynomial-kernel theorem. -/
noncomputable def firstOrderCurveGradedFinMatrix
    (D A m M μ n : ℕ) (centers : Fin n → F) (w : Fin n → F[X]) :
    Matrix (Fin (Fintype.card (FirstOrderCurveGradedRowIndex F D A m M μ n)))
      (Fin (Fintype.card ↑(firstOrderExponents D A m M μ))) F[X] :=
  (firstOrderCurveGradedConstraintMatrix D A m M μ n centers w).submatrix
    (Fintype.equivFin (FirstOrderCurveGradedRowIndex F D A m M μ n)).symm id

/-- The row weight of a compressed coefficient is its local jet grade times the curve degree. -/
noncomputable def firstOrderCurveGradedRowWeight
    (F : Type*) [Field F] (D A m M μ n ℓ : ℕ)
    (row : FirstOrderCurveGradedRowIndex F D A m M μ n) : ℕ :=
  ℓ * row.2.1.val

/-- Row weights after the fixed compressed rows are reindexed by a single `Fin`. -/
noncomputable def firstOrderCurveGradedFinRowWeight
    (F : Type*) [Field F] (D A m M μ n ℓ : ℕ)
    (i : Fin (Fintype.card (FirstOrderCurveGradedRowIndex F D A m M μ n))) : ℕ :=
  firstOrderCurveGradedRowWeight F D A m M μ n ℓ
    ((Fintype.equivFin (FirstOrderCurveGradedRowIndex F D A m M μ n)).symm i)

/-- Every entry of the actual compressed translated matrix satisfies the shifted degree bound. -/
theorem firstOrderCurveGradedConstraintMatrix_degree_le
    (D A m M μ n ℓ : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (row : FirstOrderCurveGradedRowIndex F D A m M μ n)
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ))) :
    (firstOrderCurveGradedConstraintMatrix D A m M μ n centers w row j).natDegree ≤
      ℓ * (totalJetDegree
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent -
          row.2.1.val) := by
  have h := constraintMatrix_degree_le_grade_shift m ℓ centers w hw
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))
    (row.1, firstOrderCurveGradedRowLocalIndex F D A m M μ n row) j
  simpa only [firstOrderCurveGradedConstraintMatrix,
    firstOrderCurveGradedRowLocalIndex,
    localJetDegree_firstOrderGradedTargetLowContactIndex,
    SourceColumn.totalJetDegree_exponent, Fin.sum_univ_one] using h

/-- Entries into a compressed row above the source grade are identically zero. -/
theorem firstOrderCurveGradedConstraintMatrix_eq_zero_of_grade_lt
    (D A m M μ n ℓ : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (row : FirstOrderCurveGradedRowIndex F D A m M μ n)
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)))
    (hgrade : totalJetDegree
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent <
        row.2.1.val) :
    firstOrderCurveGradedConstraintMatrix D A m M μ n centers w row j = 0 := by
  apply constraintMatrix_eq_zero_of_source_grade_lt_row_grade m ℓ centers w hw
  simpa only [firstOrderCurveGradedRowLocalIndex,
    localJetDegree_firstOrderGradedTargetLowContactIndex,
    SourceColumn.totalJetDegree_exponent, Fin.sum_univ_one] using hgrade

/-- The flattened actual matrix has the shifted row/column degree bound required by the
polynomial-kernel theorem. -/
theorem firstOrderCurveGradedFinMatrix_degree_le
    (D A m M μ n ℓ : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (i : Fin (Fintype.card (FirstOrderCurveGradedRowIndex F D A m M μ n)))
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)))
    (_hweight : firstOrderCurveGradedFinRowWeight F D A m M μ n ℓ i ≤
      ℓ * totalJetDegree
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent) :
    (firstOrderCurveGradedFinMatrix D A m M μ n centers w i j).natDegree ≤
      ℓ * totalJetDegree
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent -
        firstOrderCurveGradedFinRowWeight F D A m M μ n ℓ i := by
  let row := (Fintype.equivFin
    (FirstOrderCurveGradedRowIndex F D A m M μ n)).symm i
  have hdegree := firstOrderCurveGradedConstraintMatrix_degree_le
    D A m M μ n ℓ centers w hw row j
  change (firstOrderCurveGradedConstraintMatrix D A m M μ n centers w row j).natDegree ≤ _
  simpa only [firstOrderCurveGradedFinRowWeight, firstOrderCurveGradedRowWeight,
    row, Nat.mul_sub_left_distrib] using hdegree

/-- Flattened entries whose row weight exceeds their source-column weight are zero. -/
theorem firstOrderCurveGradedFinMatrix_eq_zero_of_weight_lt
    (D A m M μ n ℓ : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (i : Fin (Fintype.card (FirstOrderCurveGradedRowIndex F D A m M μ n)))
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)))
    (hweight : ℓ * totalJetDegree
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent <
      firstOrderCurveGradedFinRowWeight F D A m M μ n ℓ i) :
    firstOrderCurveGradedFinMatrix D A m M μ n centers w i j = 0 := by
  let row := (Fintype.equivFin
    (FirstOrderCurveGradedRowIndex F D A m M μ n)).symm i
  change firstOrderCurveGradedConstraintMatrix D A m M μ n centers w row j = 0
  apply firstOrderCurveGradedConstraintMatrix_eq_zero_of_grade_lt
    D A m M μ n ℓ centers w hw row j
  simp only [firstOrderCurveGradedFinRowWeight, firstOrderCurveGradedRowWeight] at hweight
  change totalJetDegree
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent <
    ((Fintype.equivFin
      (FirstOrderCurveGradedRowIndex F D A m M μ n)).symm i).2.1.val
  exact Nat.lt_of_mul_lt_mul_left hweight

/-- The actual sum of origin block ranks satisfies the sharp executable paper profile. -/
theorem firstOrderOriginGradedRank_le_bound (D A m M t : ℕ) :
    firstOrderOriginGradedRank F D A m M t ≤ firstOrderGradedRankBound D A m M t := by
  apply Finset.sum_le_sum
  intro s hs
  exact firstOrderOriginGradedSliceMatrix_rank_le (F := F) D A m M s t

/-! ### Actual homogeneous block images -/

/-- The part of the finite first-order support having total jet degree exactly `t`. -/
noncomputable def firstOrderGradeSpace (F : Type*) [Field F]
    (D A m M μ t : ℕ) : Submodule F (DifferentialPolynomial F 1) :=
  firstOrderSpace F D A m M μ ⊓ sourceJetGrade F 1 t

/-- The origin constraint restricted to the degree-`t` source and local-image blocks. -/
noncomputable def firstOrderGradedLocalConstraintAtZero (D A m M μ t : ℕ) :
    firstOrderGradeSpace F D A m M μ t →ₗ[F] localJetGrade F 1 t where
  toFun Q := ⟨localConstraintAt (d := 1) m 0 0 Q.1,
    localConstraintAt_zero_isWeightedHomogeneous (m := m) Q.2.2⟩
  map_add' P Q := by ext; simp
  map_smul' a Q := by ext; simp

/-- The degree-`t` row profile is the sum of actual ranks of its disjoint origin
`T`-degree blocks.  This is the unique rank profile used by shifted height counting. -/
noncomputable abbrev firstOrderGradedRank (F : Type*) [Field F]
    (D A m M t : ℕ) : ℕ :=
  firstOrderOriginGradedRank F D A m M t

/-- The complete actual graded row count through the total-degree cap `μ`. -/
noncomputable def firstOrderGradedRowCount (F : Type*) [Field F]
    (D A m M μ : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (μ + 1), firstOrderGradedRank F D A m M t

/-- The symbolic first-order matrix has the certified global rank bound over `F(Z)`.
The proof factors it through the actual global constraint map on the capped support. -/
theorem firstOrder_curve_matrix_rank_le {D A m M μ n N : ℕ}
    (hD : 1 < D) (centers : Fin n → F) (w : Fin n → F[X]) (columns : Fin N → SourceColumn 1)
    (heligible : ∀ j, (columns j).exponent ∈ firstOrderExponents D A m M μ) :
    ((constraintMatrix m centers w columns).map (algebraMap F[X] (RatFunc F))).rank ≤
      n * certifiedEnlargedRankBound 1 m M 0 := by
  classical
  let K := RatFunc F
  let φ : F[X] →+* K := algebraMap F[X] K
  let V := firstOrderSpace K D A m M μ
  let monomial (j : Fin N) : V := ⟨(columns j).polynomial, by
    apply mem_firstOrderSpace_iff.mpr
    intro u hu
    have heq : u = (columns j).exponent := by
      simpa [SourceColumn.polynomial] using MvPolynomial.support_monomial_subset hu
    exact heq ▸ heligible j⟩
  let assemble : (Fin N → K) →ₗ[K] V :=
    ∑ j, (LinearMap.smulRight (LinearMap.proj j) (monomial j))
  let constraint := firstOrderGlobalConstraint (D := D) (A := A) (m := m) (M := M) (μ := μ)
    (fun i ↦ φ (Polynomial.C (centers i))) (fun i ↦ φ (w i))
  let coefficients : (Fin n → LocalPolynomial K 1) →ₗ[K]
      ((Fin n × LowContactIndex 1 m) → K) :=
    LinearMap.pi fun row ↦ MvPolynomial.lcoeff K row.2.1 ∘ₗ LinearMap.proj row.1
  let mat := (constraintMatrix m centers w columns).map φ
  have hfactor : mat.mulVecLin = coefficients ∘ₗ constraint ∘ₗ assemble := by
    apply LinearMap.ext
    intro v
    funext row
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      LinearMap.comp_apply, coefficients, LinearMap.pi_apply, MvPolynomial.lcoeff_apply,
      LinearMap.proj_apply, assemble, LinearMap.sum_apply, map_sum, LinearMap.smulRight_apply,
      map_smul]
    change (∑ j, φ (constraintMatrix m centers w columns row j) * v j) = _
    simp only [constraint, firstOrderGlobalConstraint, LinearMap.pi_apply,
      firstOrderLocalConstraintAt, LinearMap.domRestrict_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hentry : constraintMatrix m centers w columns row j =
        MvPolynomial.coeff row.2.1
          (localConstraintAt m (Polynomial.C (centers row.1)) (w row.1)
            (columns j).polynomial) := by
      simp [constraintMatrix, localConstraintCoordinatesAt, lowContactCoefficients,
        localConstraintAt, projectLowContact, coeff_filterLocalMonomials, row.2.2]
    rw [hentry]
    rw [← MvPolynomial.coeff_map, map_localConstraintAt]
    simp [monomial, SourceColumn.polynomial, mul_comm]
  let _ : Module.Finite K V := Module.Finite.of_basis (firstOrderSpaceBasis K D A m M μ)
  change Module.finrank K mat.mulVecLin.range ≤ _
  rw [hfactor]
  apply (finrank_range_comp_le_outer (coefficients ∘ₗ constraint) assemble).trans
  rw [LinearMap.range_comp]
  apply (Submodule.finrank_map_le coefficients constraint.range).trans
  simpa [constraint] using
    (finrank_firstOrderGlobalConstraint_le (A := A) (m := m) (M := M) (μ := μ) hD
      (fun i ↦ φ (Polynomial.C (centers i)))
      (fun i ↦ φ (w i)))

end

end ReedSolomon.HiddenDerivative
