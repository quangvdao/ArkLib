/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.LocalRank
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.ReceivedLine
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SymbolicBandMargin


/-!
# Symbolic interpolation on the asymmetric band

This file identifies symbolic received-line columns with columns of the canonical asymmetric-band
local matrix, sums the ranks of the point blocks, and applies the primitive polynomial-kernel
theorem to the full band basis.
-/

open PolynomialDifferential


noncomputable section

open Polynomial

namespace ReedSolomon.HiddenDerivative

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F]
variable {d D m W Cmin Cmax : ℕ} {L : ℝ}

namespace SymbolicBandInterpolation

open SymbolicReceivedInterpolation

/-- One block of a matrix whose rows are indexed by a product. -/
def Matrix.rowBlock {K : Type*} {ι ρ κ : Type*}
    (A : Matrix (ι × ρ) κ K) (i : ι) : Matrix ρ κ K :=
  fun row column => A (i, row) column

/-- A matrix with a finite product row type has rank at most the sum of its block ranks. -/
theorem Matrix.rank_prod_rows_le_sum
    {K : Type*} [Field K] {ι ρ κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix (ι × ρ) κ K) :
    A.rank ≤ ∑ i, (Matrix.rowBlock A i).rank := by
  let Φ := A.mulVecLin
  let block : ι → Matrix ρ κ K := Matrix.rowBlock A
  let φ := fun i => (block i).mulVecLin
  let includeRange : Φ.range →ₗ[K] (∀ i, (φ i).range) := {
    toFun y i := ⟨(fun row => y.1 (i, row)), by
      rcases y.2 with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      ext row
      simpa [Φ, φ, block, Matrix.rowBlock, Matrix.mulVecLin_apply, Matrix.mulVec] using
        congrFun hv (i, row)⟩
    map_add' x y := by
      ext i row
      rfl
    map_smul' a x := by
      ext i row
      rfl
  }
  have hinjective : Function.Injective includeRange := by
    intro x y hxy
    apply Subtype.ext
    funext row
    have hi := congrArg Subtype.val (congrFun hxy row.1)
    exact congrFun hi row.2
  change Module.finrank K A.mulVecLin.range ≤ _
  calc
    Module.finrank K Φ.range ≤ Module.finrank K (∀ i, (φ i).range) :=
      LinearMap.finrank_le_finrank_of_injective hinjective
    _ = ∑ i, Module.finrank K (φ i).range := Module.finrank_pi_fintype K
    _ = ∑ i, (Matrix.rowBlock A i).rank := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show φ i = (Matrix.rowBlock A i).mulVecLin by rfl]
      rfl

/-- Interpret a band-eligible symbolic column as an index of the canonical band matrix. -/
def bandColumnIndex {N : ℕ} (hD : 0 < D) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, AsymmetricBandEligible D d m W Cmin Cmax L (columns j).exponent)
    (j : Fin N) : AsymmetricBandIndex D d m W Cmin Cmax L hD :=
  ⟨(columns j).exponent, mem_asymmetricBandExponents.mpr (hband j)⟩

private theorem map_unscaledLocalImage
    {R E : Type*} [CommRing R] [CommRing E] (φ : R →+* E)
    (center received : R) (v : JetVariable d) :
    MvPolynomial.map φ (unscaledLocalImage d center received v) =
      unscaledLocalImage d (φ center) (φ received) v := by
  rcases v with _ | j
  · simp [unscaledLocalImage]
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp [unscaledLocalImage, localCorrection]
    · simp [unscaledLocalImage]

private theorem localConstraintCoordinatesAt_monomial_map
    {R E : Type*} [CommRing R] [CommRing E] (φ : R →+* E)
    (center received : R) (u : JetVariable d →₀ ℕ) (row : LowContactIndex d m) :
    φ (localConstraintCoordinatesAt m center received (MvPolynomial.monomial u 1) row) =
      localConstraintCoordinatesAt m (φ center) (φ received)
        (MvPolynomial.monomial u 1) row := by
  unfold localConstraintCoordinatesAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, lowContactCoefficients,
    LinearMap.pi_apply, MvPolynomial.lcoeff_apply]
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp only [unscaledLocalSubstitution, MvPolynomial.bind₁_monomial,
    map_one, map_mul, map_prod, map_pow]
  simp_rw [map_unscaledLocalImage φ center received]

/-- One mapped received-line point block is a column submatrix of the canonical band matrix over
the rational-function field. -/
theorem receivedLine_block_eq_canonical_submatrix {n N : ℕ}
    (hD : 0 < D) (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, AsymmetricBandEligible D d m W Cmin Cmax L (columns j).exponent)
    (i : Fin n) :
    (fun row j => algebraMap F[X] (RatFunc F)
      (matrix m centers f g columns (i, row) j) :
        Matrix (LowContactIndex d m) (Fin N) (RatFunc F)) =
      (asymmetricBandLocalCoordinateMatrix (R := RatFunc F) (d := d) (m := m)
        (W := W) (Cmin := Cmin) (Cmax := Cmax) (L := L) hD
        (algebraMap F[X] (RatFunc F) (Polynomial.C (centers i)))
        (algebraMap F[X] (RatFunc F) (receivedLine (f i) (g i)))).submatrix
          id (bandColumnIndex hD columns hband) := by
  ext row j
  rw [Matrix.submatrix_apply, id_eq]
  simp only [matrix, asymmetricBandLocalCoordinateMatrix_apply,
    bandColumnIndex, SourceColumn.polynomial]
  exact localConstraintCoordinatesAt_monomial_map
    (algebraMap F[X] (RatFunc F)) (Polynomial.C (centers i))
      (receivedLine (f i) (g i)) (columns j).exponent row

/-- Every mapped received-line point block has rank at most the source-field actual local rank. -/
theorem receivedLine_block_rank_le_base_actual {n N : ℕ}
    (hD : 0 < D) (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, AsymmetricBandEligible D d m W Cmin Cmax L (columns j).exponent)
    (i : Fin n) :
    Matrix.rank ((fun row j => algebraMap F[X] (RatFunc F)
      (matrix m centers f g columns (i, row) j)) :
        Matrix (LowContactIndex d m) (Fin N) (RatFunc F)) ≤
      Module.finrank F (LinearMap.range
        (asymmetricBandLocalConstraint (R := F) (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0)) := by
  rw [receivedLine_block_eq_canonical_submatrix hD centers f g columns hband i]
  exact (Matrix.rank_submatrix_le _ id (bandColumnIndex hD columns hband)).trans
    (rank_asymmetricBandLocalCoordinateMatrix_le_base_actual
      (F := F) hD
      (algebraMap F[X] (RatFunc F) (Polynomial.C (centers i)))
      (algebraMap F[X] (RatFunc F) (receivedLine (f i) (g i))))

/-- The complete mapped symbolic matrix has rank at most `n` times the source-field actual local
rank. -/
theorem receivedLine_matrix_rank_le_base_actual {n N : ℕ}
    (hD : 0 < D) (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, AsymmetricBandEligible D d m W Cmin Cmax L (columns j).exponent) :
    ((matrix m centers f g columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤
      n * Module.finrank F (LinearMap.range
        (asymmetricBandLocalConstraint (R := F) (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0)) := by
  let A := (matrix m centers f g columns).map (algebraMap F[X] (RatFunc F))
  calc
    A.rank ≤ ∑ i, (Matrix.rowBlock A i).rank :=
      Matrix.rank_prod_rows_le_sum A
    _ ≤ ∑ _ : Fin n, Module.finrank F (LinearMap.range
        (asymmetricBandLocalConstraint (R := F) (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0)) := by
      apply Finset.sum_le_sum
      intro i _
      exact receivedLine_block_rank_le_base_actual hD centers f g columns hband i
    _ = _ := by simp

/-- Recover `SourceColumn` coordinates from an arbitrary global exponent. -/
def SourceColumn.ofExponent (u : JetVariable d →₀ ℕ) : SourceColumn d where
  x := u none
  y₀ := u (some 0)
  higher j := u (some j.succ)

@[simp] theorem SourceColumn.exponent_ofExponent (u : JetVariable d →₀ ℕ) :
    (SourceColumn.ofExponent u).exponent = u := by
  ext v
  rcases v with _ | j
  · simp [SourceColumn.ofExponent, SourceColumn.exponent]
  · induction j using Fin.cases with
    | zero => simp [SourceColumn.ofExponent, SourceColumn.exponent]
    | succ j =>
      simp only [SourceColumn.ofExponent, SourceColumn.exponent, Finsupp.add_apply,
        Finsupp.single_apply, Option.some.injEq, reduceCtorEq,
        ite_false, zero_add]
      rw [if_neg (by
        intro h
        have := congrArg Fin.val h
        simp at this), zero_add]
      change Finsupp.applyAddHom (some j.succ)
        (∑ k : Fin d, Finsupp.single (some k.succ) (u (some k.succ))) = _
      rw [map_sum]
      calc
        ∑ k : Fin d, Finsupp.applyAddHom (some j.succ)
            (Finsupp.single (some k.succ) (u (some k.succ))) =
            Finsupp.applyAddHom (some j.succ)
              (Finsupp.single (some j.succ) (u (some j.succ))) := by
          apply Fintype.sum_eq_single j
          intro k hkj
          simp [hkj]
        _ = u (some j.succ) := by simp

/-- Canonical enumeration of every asymmetric-band monomial as a `SourceColumn`. -/
def bandColumns (hD : 0 < D) :
    Fin (Fintype.card (AsymmetricBandIndex D d m W Cmin Cmax L hD)) → SourceColumn d :=
  fun j => SourceColumn.ofExponent
    (((Fintype.equivFin (AsymmetricBandIndex D d m W Cmin Cmax L hD)).symm j).1)

@[simp] theorem bandColumns_exponent (hD : 0 < D)
    (j : Fin (Fintype.card (AsymmetricBandIndex D d m W Cmin Cmax L hD))) :
    (bandColumns (d := d) (m := m) (W := W) (Cmin := Cmin) (Cmax := Cmax)
      (L := L) hD j).exponent =
      ((Fintype.equivFin (AsymmetricBandIndex D d m W Cmin Cmax L hD)).symm j).1 := by
  simp [bandColumns]

theorem bandColumns_injective (hD : 0 < D) :
    Function.Injective (bandColumns (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD) := by
  intro i j hij
  apply (Fintype.equivFin (AsymmetricBandIndex D d m W Cmin Cmax L hD)).symm.injective
  apply Subtype.ext
  rw [← bandColumns_exponent hD i, ← bandColumns_exponent hD j, hij]

theorem bandColumns_eligible (hD : 0 < D)
    (j : Fin (Fintype.card (AsymmetricBandIndex D d m W Cmin Cmax L hD))) :
    AsymmetricBandEligible D d m W Cmin Cmax L
      (bandColumns (d := d) (m := m) (W := W) (Cmin := Cmin) (Cmax := Cmax)
        (L := L) hD j).exponent := by
  rw [bandColumns_exponent]
  exact mem_asymmetricBandExponents.mp
    ((Fintype.equivFin (AsymmetricBandIndex D d m W Cmin Cmax L hD)).symm j).2

/-- Under the prescribed slack bound, the strict band cutoff gives the sharp integer bound
`Y₀ ≤ 2m - 1`. -/
theorem y₀_le_two_mul_sub_one_of_eligible {g : ℝ}
    (hD : 0 < D) (hg : g ≤ 1) (hm : 0 < m)
    {u : JetVariable d →₀ ℕ}
    (hu : AsymmetricBandEligible D d m W Cmin Cmax
      ((D : ℝ) * m * (1 + g)) u) :
    u (some 0) ≤ 2 * m - 1 := by
  have hcoord : u (some 0) ≤ totalJetDegree u := Finsupp.le_degree 0 u.some
  have hDReal : (0 : ℝ) < D := by exact_mod_cast hD
  have hcut := hu.2.2.2.2
  push_cast at hcut
  have hL : (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * (2 * m) := by
    have hnonneg : (0 : ℝ) ≤ (D : ℝ) * m := by positivity
    calc
      (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * m * 2 := by
        exact mul_le_mul_of_nonneg_left (by linarith) hnonneg
      _ = (D : ℝ) * (2 * m) := by ring
  have htotalReal : (totalJetDegree u : ℝ) < 2 * m := by
    have hx : (0 : ℝ) ≤ u none := by positivity
    have hmul : (D : ℝ) * totalJetDegree u < (D : ℝ) * (2 * m) :=
      (le_add_of_nonneg_left hx).trans_lt (hcut.trans_le hL)
    exact lt_of_mul_lt_mul_left hmul hDReal.le
  have htotal : totalJetDegree u < 2 * m := by exact_mod_cast htotalReal
  omega

/-- A fixed dimension margin produces a primitive symbolic interpolant on the full asymmetric
band, with an explicit challenge-degree bound and no bad challenge over any extension field. -/
theorem exists_symbolic_band_interpolant_of_fixed_margin {n ν : ℕ}
    (hD : 0 < D) (hν : 0 < ν) (centers f g : Fin n → F)
    (hy₀ : ∀ u, AsymmetricBandEligible D d m W Cmin Cmax L u → u (some 0) ≤ ν)
    (hmargin : (456976 / 455625 : ℝ) * n *
      Module.finrank F (LinearMap.range
        (asymmetricBandLocalConstraint (R := F) (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0)) <
      Module.finrank F (asymmetricBandSpace F D d m W Cmin Cmax L hD)) :
    let N := Fintype.card (AsymmetricBandIndex D d m W Cmin Cmax L hD)
    let columns := bandColumns (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD
    ∃ v : Fin N → F[X],
      v ≠ 0 ∧
        Matrix.mulVec (matrix m centers f g columns) v = 0 ∧
          (∀ j, (v j).natDegree ≤ n *
            Module.finrank F (LinearMap.range
              (asymmetricBandLocalConstraint (R := F) (d := d) (m := m) (W := W)
                (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0)) * ν /
              (N - n * Module.finrank F (LinearMap.range
                (asymmetricBandLocalConstraint (R := F) (d := d) (m := m) (W := W)
                  (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0)))) ∧
            (∀ j, ((v j).natDegree : ℝ) < 338 * ν) ∧
              Ideal.span (Set.range v) = ⊤ ∧
                (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
                  MvPolynomial.map (Polynomial.eval₂RingHom ι z)
                    (interpolant columns v) ≠ 0) ∧
                  (∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
                    (receivedLine (f i) (g i)) (interpolant columns v)) ∧
                    ∀ j, AsymmetricBandEligible D d m W Cmin Cmax L
                      (columns j).exponent := by
  dsimp only
  let columns := bandColumns (d := d) (m := m) (W := W)
    (Cmin := Cmin) (Cmax := Cmax) (L := L) hD
  let r₀ := Module.finrank F (LinearMap.range
    (asymmetricBandLocalConstraint (R := F) (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0))
  let N := Fintype.card (AsymmetricBandIndex D d m W Cmin Cmax L hD)
  have hband : ∀ j, AsymmetricBandEligible D d m W Cmin Cmax L
      (columns j).exponent := bandColumns_eligible hD
  have hcolumns : Function.Injective columns := bandColumns_injective hD
  have hy₀' : ∀ j, (columns j).y₀ ≤ ν := by
    intro j
    simpa [SourceColumn.exponent] using hy₀ (columns j).exponent (hband j)
  have hdim : Module.finrank F (asymmetricBandSpace F D d m W Cmin Cmax L hD) = N := by
    rw [finrank_asymmetricBandSpace_eq_card hD, ← Fintype.card_coe]
  have hmargin' : (456976 / 455625 : ℝ) * ((n * r₀ : ℕ) : ℝ) < N := by
    rw [← hdim]
    simpa only [r₀, Nat.cast_mul, mul_assoc] using hmargin
  have hN : n * r₀ < N := by
    have hscale : ((n * r₀ : ℕ) : ℝ) ≤
        (456976 / 455625 : ℝ) * ((n * r₀ : ℕ) : ℝ) := by
      have hnonneg : (0 : ℝ) ≤ ((n * r₀ : ℕ) : ℝ) := by positivity
      nlinarith
    have hltReal : ((n * r₀ : ℕ) : ℝ) < (N : ℝ) := hscale.trans_lt hmargin'
    exact_mod_cast hltReal
  have hrank : ((matrix m centers f g columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ n * r₀ := by
    exact receivedLine_matrix_rank_le_base_actual hD centers f g columns hband
  obtain ⟨v, hv, hkernel, hdegree, hprimitive, hnozero, hconstraints⟩ :=
    exists_symbolic_received_line_interpolant_of_rank_le
      m ν r₀ centers f g columns hcolumns hy₀' hrank hN
  have hheight : ∀ j, ((v j).natDegree : ℝ) < 338 * ν := by
    intro j
    have hdegreeReal : ((v j).natDegree : ℝ) ≤
        ((n * r₀ * ν / (N - n * r₀) : ℕ) : ℝ) := by
      exact_mod_cast hdegree j
    exact hdegreeReal.trans_lt
      (fixed_margin_kernel_height_lt N (n * r₀) ν hν hmargin').2
  exact ⟨v, hv, hkernel, hdegree, hheight, hprimitive, hnozero, hconstraints, hband⟩

end SymbolicBandInterpolation

end ReedSolomon.HiddenDerivative
