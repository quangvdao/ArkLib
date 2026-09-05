/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.IntermediateGapLocalRank
import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.SymbolicBandCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.InterpolationDimensionBridge

/-! # The order-one symbolic certificate for the intermediate gap -/

noncomputable section

open Polynomial

namespace ReedSolomon.HiddenDerivative

open MvPolynomial
open scoped BigOperators

namespace IntermediateGapCertificate

open SymbolicReceivedInterpolation
open SymbolicBandInterpolation

variable {F : Type*} [Field F]

/-- Canonical exact-space monomial columns. -/
def exactColumns {D A : ℕ} (hD : 1 < D) :
    Fin (Fintype.card (ExactInterpolationIndex D A 1 64 16 0 hD)) → SourceColumn 1 :=
  fun j => SymbolicBandInterpolation.SourceColumn.ofExponent
    (((Fintype.equivFin (ExactInterpolationIndex D A 1 64 16 0 hD)).symm j).1)

@[simp] theorem exactColumns_exponent {D A : ℕ} (hD : 1 < D)
    (j : Fin (Fintype.card (ExactInterpolationIndex D A 1 64 16 0 hD))) :
    (exactColumns hD j).exponent =
      ((Fintype.equivFin (ExactInterpolationIndex D A 1 64 16 0 hD)).symm j).1 := by
  simp [exactColumns, SymbolicBandInterpolation.SourceColumn.exponent_ofExponent]

theorem exactColumns_injective {D A : ℕ} (hD : 1 < D) :
    Function.Injective (exactColumns (A := A) hD) := by
  intro i j hij
  apply (Fintype.equivFin (ExactInterpolationIndex D A 1 64 16 0 hD)).symm.injective
  apply Subtype.ext
  simpa only [← exactColumns_exponent hD i, ← exactColumns_exponent hD j] using
    congrArg SourceColumn.exponent hij

theorem exactColumns_eligible {D A : ℕ} (hD : 1 < D)
    (j : Fin (Fintype.card (ExactInterpolationIndex D A 1 64 16 0 hD))) :
    ExactInterpolationEligibleExponent D A 1 64 16 0 (exactColumns hD j).exponent := by
  rw [exactColumns_exponent]
  exact mem_exactInterpolationExponents.mp
    ((Fintype.equivFin (ExactInterpolationIndex D A 1 64 16 0 hD)).symm j).property

theorem exactColumns_y₀_le {D A : ℕ} (hD : 1 < D) (hAD : 64 * A ≤ 120 * D)
    (j : Fin (Fintype.card (ExactInterpolationIndex D A 1 64 16 0 hD))) :
    (exactColumns hD j).y₀ ≤ 119 := by
  let u := (exactColumns hD j).exponent
  have hw : exactInterpolationMonomialWeight D u < 64 * A :=
    (exactColumns_eligible hD j).2.2
  have hyw : D * u (some 0) ≤ exactInterpolationMonomialWeight D u := by
    rw [exactInterpolationMonomialWeight_eq]
    apply le_trans ?_ (Nat.le_add_left _ _)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    rw [Fin.sum_univ_two]
    simp [Nat.mul_comm]
  have : D * u (some 0) < 120 * D := hyw.trans_lt (hw.trans_le hAD)
  have : u (some 0) < 120 := by nlinarith
  simpa [u, exactColumns, SymbolicBandInterpolation.SourceColumn.ofExponent] using
    (Nat.le_sub_one_of_lt this)

/-- Canonical coordinate matrix of the exact order-one local map. -/
def exactLocalCoordinateMatrix {R : Type*} [Field R] {D A : ℕ} (hD : 1 < D)
    (center received : R) :
    Matrix (LowContactIndex 1 64) (ExactInterpolationIndex D A 1 64 16 0 hD) R :=
  fun row column ↦ localConstraintCoordinatesAt 64 center received
    (MvPolynomial.monomial column.1 1) row

/-- The exact coordinate matrix has rank at most the actual polynomial-valued local map. -/
theorem rank_exactLocalCoordinateMatrix_le_actual
    {R : Type*} [Field R] {D A : ℕ} (hD : 1 < D) (center received : R) :
    (exactLocalCoordinateMatrix (A := A) hD center received).rank ≤
      Module.finrank R (LinearMap.range
        (exactLocalConstraintAt (D := D) (A := A) (M := 16) (W := 0)
          hD 64 center received)) := by
  let b := exactInterpolationSpaceBasis R D A 1 64 16 0 hD
  let f := (localConstraintCoordinatesAt (d := 1) 64 center received).domRestrict
    (exactInterpolationSpace R D A 1 64 16 0 hD)
  let _ : Module.Finite R (exactInterpolationSpace R D A 1 64 16 0 hD) :=
    Module.Finite.of_basis b
  rw [Matrix.rank_eq_finrank_span_cols]
  have hspan : Submodule.span R
      (Set.range (exactLocalCoordinateMatrix (A := A) hD center received).col) ≤
      LinearMap.range f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨column, rfl⟩
    refine ⟨b column, ?_⟩
    ext row
    simp only [Matrix.col_apply, exactLocalCoordinateMatrix]
    change localConstraintCoordinatesAt 64 center received (b column).1 row = _
    have hb : ((b column).1 : DifferentialPolynomial R 1) =
        MvPolynomial.monomial column.1 1 := by
      have heq : exactInterpolationPolynomial (F := R) hD
          (Finsupp.single column (1 : R)) = b column := by
        exact b.repr_symm_single_one column
      calc
        ((b column).1 : DifferentialPolynomial R 1) =
            (exactInterpolationPolynomial (F := R) hD
              (Finsupp.single column (1 : R))).1 := congrArg Subtype.val heq.symm
        _ = _ := exactInterpolationPolynomial_single (F := R) hD column (1 : R)
    rw [hb]
  have hcoord : Module.finrank R (LinearMap.range f) ≤
      Module.finrank R (LinearMap.range
        (exactLocalConstraintAt (D := D) (A := A) (M := 16) (W := 0)
          hD 64 center received)) := by
    have hcomp : f = (lowContactCoefficients (R := R) (d := 1) 64).comp
        (exactLocalConstraintAt (D := D) (A := A) (M := 16) (W := 0)
          hD 64 center received) := by
      apply LinearMap.ext
      intro Q
      ext row
      simp [f, localConstraintCoordinatesAt, exactLocalConstraintAt, localConstraintAt,
        lowContactCoefficients, projectLowContact, coeff_filterLocalMonomials, row.2]
    rw [hcomp, LinearMap.range_comp]
    exact Submodule.finrank_map_le _ _
  exact (Submodule.finrank_mono hspan).trans hcoord

private theorem map_unscaledLocalImage
    {R E : Type*} [CommRing R] [CommRing E] (φ : R →+* E)
    (center received : R) (v : JetVariable 1) :
    MvPolynomial.map φ (unscaledLocalImage 1 center received v) =
      unscaledLocalImage 1 (φ center) (φ received) v := by
  rcases v with _ | j
  · simp [unscaledLocalImage]
  · refine Fin.cases ?_ (fun i ↦ ?_) j
    · simp [unscaledLocalImage, localCorrection]
    · simp [unscaledLocalImage]

private theorem localConstraintCoordinatesAt_monomial_map
    {R E : Type*} [CommRing R] [CommRing E] (φ : R →+* E)
    (center received : R) (u : JetVariable 1 →₀ ℕ) (row : LowContactIndex 1 64) :
    φ (localConstraintCoordinatesAt 64 center received (MvPolynomial.monomial u 1) row) =
      localConstraintCoordinatesAt 64 (φ center) (φ received)
        (MvPolynomial.monomial u 1) row := by
  unfold localConstraintCoordinatesAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, lowContactCoefficients,
    LinearMap.pi_apply, MvPolynomial.lcoeff_apply]
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp only [unscaledLocalSubstitution, MvPolynomial.bind₁_monomial,
    map_one, map_mul, map_prod, map_pow]
  simp_rw [map_unscaledLocalImage φ center received]

/-- Each point block of the symbolic exact-space matrix has the certified actual rank. -/
theorem receivedLine_block_rank_le {D A n : ℕ} (hD : 1 < D)
    (centers f g : Fin n → F) (i : Fin n) :
    Matrix.rank ((fun row j ↦ algebraMap F[X] (RatFunc F)
      (matrix 64 centers f g (exactColumns (A := A) hD) (i, row) j)) :
        Matrix (LowContactIndex 1 64)
          (Fin (Fintype.card (ExactInterpolationIndex D A 1 64 16 0 hD))) (RatFunc F)) ≤
      28152 := by
  let e := (Fintype.equivFin (ExactInterpolationIndex D A 1 64 16 0 hD)).symm
  have heq : (fun row j ↦ algebraMap F[X] (RatFunc F)
      (matrix 64 centers f g (exactColumns (A := A) hD) (i, row) j)) =
      (exactLocalCoordinateMatrix (R := RatFunc F) (A := A) hD
        (algebraMap F[X] (RatFunc F) (Polynomial.C (centers i)))
        (algebraMap F[X] (RatFunc F) (receivedLine (f i) (g i)))).submatrix id e := by
    ext row j
    rw [Matrix.submatrix_apply, id_eq]
    simp only [matrix, exactLocalCoordinateMatrix]
    rw [SourceColumn.polynomial, exactColumns_exponent]
    exact localConstraintCoordinatesAt_monomial_map
      (algebraMap F[X] (RatFunc F)) (Polynomial.C (centers i))
        (receivedLine (f i) (g i))
          (((Fintype.equivFin (ExactInterpolationIndex D A 1 64 16 0 hD)).symm j).1) row
  rw [heq]
  exact (Matrix.rank_submatrix_le _ id e).trans
    ((rank_exactLocalCoordinateMatrix_le_actual (R := RatFunc F) (A := A) hD _ _).trans
      (finrank_exactLocalConstraintAt_orderOne_le (F := RatFunc F) hD _ _))

/-- The full mapped symbolic matrix has rank at most `28152 n`. -/
theorem receivedLine_matrix_rank_le {D A n : ℕ} (hD : 1 < D)
    (centers f g : Fin n → F) :
    ((matrix 64 centers f g (exactColumns (A := A) hD)).map
      (algebraMap F[X] (RatFunc F))).rank ≤ n * 28152 := by
  let B := (matrix 64 centers f g (exactColumns (A := A) hD)).map
    (algebraMap F[X] (RatFunc F))
  calc
    B.rank ≤ ∑ i, (Matrix.rowBlock B i).rank := Matrix.rank_prod_rows_le_sum B
    _ ≤ ∑ _ : Fin n, 28152 := by
      apply Finset.sum_le_sum
      intro i _
      exact receivedLine_block_rank_le (A := A) hD centers f g i
    _ = n * 28152 := by simp

/-- The symbolic intermediate-gap output, retaining the exact interpolation-space semantics. -/
structure Certificate (F : Type*) [Field F] {n : ℕ} (D A k : ℕ)
    (centers : Fin n ↪ F) (f g : Fin n → F) where
  Q : DifferentialPolynomial F[X] 1
  challengeDegree_le : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ 1449
  support_eligible : ∀ u ∈ Q.support,
    ExactInterpolationEligibleExponent D A 1 64 16 0 u
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
      ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (ι (centers i)) = ι (f i) + z * ι (g i)) →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

/-- Specialization of the canonical exact-column interpolant remains in the exact space. -/
theorem map_interpolant_mem_exactSpace {D A : ℕ} (hD : 1 < D)
    (v : Fin (Fintype.card (ExactInterpolationIndex D A 1 64 16 0 hD)) → F[X])
    {E : Type*} [Field E] (ι : F →+* E) (z : E) :
    MvPolynomial.map (Polynomial.eval₂RingHom ι z)
      (interpolant (exactColumns hD) v) ∈ exactInterpolationSpace E D A 1 64 16 0 hD := by
  rw [interpolant, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [MvPolynomial.map_monomial, monomial_mem_exactInterpolationSpace]
  exact Or.inl (exactColumns_eligible hD j)

/-- The actual dimension margin `30464 n` yields the primitive order-one certificate with
coefficient challenge degree at most `1449`. -/
theorem exists_certificate {D A k n : ℕ} (hD : 1 < D) (hn : 0 < n)
    (hAD : 64 * A ≤ 120 * D) (hbudget : 0 < 64 * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (f g : Fin n → F)
    (hdim : 30464 * n ≤
      Module.finrank F (exactInterpolationSpace F D A 1 64 16 0 hD)) :
    Nonempty (Certificate F D A k centers f g) := by
  let N := Fintype.card (ExactInterpolationIndex D A 1 64 16 0 hD)
  let columns : Fin N → SourceColumn 1 := exactColumns hD
  have hNcard : N = Module.finrank F (exactInterpolationSpace F D A 1 64 16 0 hD) := by
    symm
    simpa [N] using
      (finrank_exactInterpolationSpace_eq_card (F := F) (D := D) (A := A)
        (d := 1) (m := 64) (M := 16) (W := 0) hD)
  have hN : n * 28152 < N := by
    rw [hNcard]
    exact (by omega : n * 28152 < 30464 * n).trans_le hdim
  obtain ⟨v, _hv, _hkernel, hvdeg, _hprimitive, hnozero, hconstraints⟩ :=
    exists_symbolic_received_line_interpolant_of_rank_le
      64 119 28152 (fun i ↦ centers i) f g columns
        (exactColumns_injective hD) (exactColumns_y₀_le hD hAD)
        (receivedLine_matrix_rank_le hD (fun i ↦ centers i) f g) hN
  have hheight : ∀ j, (v j).natDegree ≤ 1449 := by
    intro j
    refine (hvdeg j).trans ?_
    rw [Nat.div_le_iff_le_mul (Nat.sub_pos_of_lt hN)]
    have hdimN : 30464 * n ≤ N := hNcard.symm ▸ hdim
    omega
  let Q : DifferentialPolynomial F[X] 1 := interpolant columns v
  have hvlt : ∀ j, (v j).natDegree < 1450 := by
    intro j
    simpa using Nat.lt_succ_of_le (hheight j)
  have hchallenge : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ 1449 := by
    intro u
    have hlt := coeff_interpolant_natDegree_lt columns
      (exactColumns_injective hD) v (by omega : 0 < 1450)
      hvlt u
    simpa [Q] using Nat.le_sub_one_of_lt hlt
  have helig : ∀ u ∈ Q.support, ExactInterpolationEligibleExponent D A 1 64 16 0 u := by
    have hQ : Q ∈ exactInterpolationSpace F[X] D A 1 64 16 0 hD := by
      dsimp only [Q]
      rw [interpolant]
      apply Submodule.sum_mem
      intro j _
      rw [monomial_mem_exactInterpolationSpace]
      exact Or.inl (exactColumns_eligible hD j)
    exact mem_exactInterpolationSpace_iff.mp hQ
  refine ⟨⟨Q, hchallenge, helig, ?_⟩⟩
  intro E _ ι z
  have hQnonzero : MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 := by
    dsimp only [Q]
    exact hnozero ι z
  refine ⟨hQnonzero, ?_⟩
  intro indices P hP hcard hagree
  have hPnat : P.natDegree ≤ D := by
    by_cases hz : P = 0
    · simp [hz]
    · have := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hP
      omega
  let φ := Polynomial.eval₂RingHom ι z
  have hconstraintsE : ∀ i, SatisfiesLocalConstraints 64 (ι (centers i))
      (ι (f i) + z * ι (g i)) (MvPolynomial.map φ Q) := by
    intro i
    have hbase : SatisfiesLocalConstraints 64 (Polynomial.C (centers i))
        (receivedLine (f i) (g i)) Q := by
      dsimp only [Q]
      exact hconstraints i
    have hi := SatisfiesLocalConstraints.map φ 64 (Polynomial.C (centers i))
      (receivedLine (f i) (g i)) Q hbase
    change SatisfiesLocalConstraints 64
      (Polynomial.eval₂ ι z (Polynomial.C (centers i)))
      (Polynomial.eval₂ ι z (receivedLine (f i) (g i)))
      (MvPolynomial.map φ Q) at hi
    simpa only [Polynomial.eval₂_C, receivedLine, Polynomial.eval₂_add,
      Polynomial.eval₂_mul, Polynomial.eval₂_X] using hi
  apply differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements
    hbudget hD (fun i ↦ ι (centers i)) (fun i ↦ ι (f i) + z * ι (g i)) indices
      (by
        dsimp only [Q]
        exact map_interpolant_mem_exactSpace hD v ι z)
      hconstraintsE P hPnat
  · intro i hi j hj hij
    exact centers.injective (ι.injective hij)
  · exact hcard
  · exact hagree

end IntermediateGapCertificate
end ReedSolomon.HiddenDerivative
