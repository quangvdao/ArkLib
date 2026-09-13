/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayIdentityCorrectness
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Fraction-field factorization of the dense Macaulay determinant

This file isolates the remaining algebra in Macaulay's universal determinant
quotient.  The executable non-reduced minor is first identified with the
corresponding principal block of the full matrix.  After embedding coefficient
polynomials into their fraction field, that block is invertible, and the Schur
complement formula factors the full determinant by the computed extraneous
factor.

The final polynomial divisibility theorem is therefore equivalent to descent
of one explicit Schur determinant from the fraction field.  Establishing that
descent from the Macaulay row structure remains the nonempty-minor identity;
it is not assumed or packaged as input here.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.MacaulayQuotient

open CPoly CPoly.CMvPolynomial
open DenseMacaulay

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

noncomputable local instance parameterIsDomain (n : ℕ) :
    IsDomain (Parameters n F) :=
  (CPoly.polyRingEquiv (n := n + 2) (R := F)).isDomain_iff.mpr inferInstance

/-- Predicate selecting exactly the rows retained by the executable
extraneous-minor construction. -/
def IsExtraneousIndex {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (i : Fin (basis system).length) : Prop :=
  nonReducedB system (basis system)[i] = true

local instance isExtraneousIndexDecidablePred {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    DecidablePred (IsExtraneousIndex system) :=
  fun i => decidable_of_iff
    (nonReducedB system (basis system)[i] = true) (by rfl)

/-- The subtype presentation of the non-reduced block. -/
abbrev ExtraneousSubtype {n : ℕ} (system : Fin n → CMvPolynomial n F) :=
  {i : Fin (basis system).length // IsExtraneousIndex system i}

/-- The stored filtered-list indexing and the principal-block subtype index
the same rows. -/
noncomputable def extraneousSubtypeEquiv {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    ExtraneousIndex system ≃ ExtraneousSubtype system :=
  ((extraneousIndices_nodup system).getEquiv (extraneousIndices system)).trans <|
    Equiv.subtypeEquivRight fun i => by
      simp [extraneousIndices, IsExtraneousIndex]

noncomputable local instance extraneousSubtypeFintype {n : ℕ}
    (system : Fin n → CMvPolynomial n F) : Fintype (ExtraneousSubtype system) :=
  Fintype.ofEquiv (ExtraneousIndex system) (extraneousSubtypeEquiv system)

noncomputable local instance reducedSubtypeFintype {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Fintype {i // ¬IsExtraneousIndex system i} :=
  Fintype.ofFinite _

omit [BEq F] [LawfulBEq F] in
/-- The stored extraneous index has the same underlying full-matrix index as
its subtype presentation. -/
@[simp]
theorem extraneousSubtypeEquiv_coe {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (i : ExtraneousIndex system) :
    ((extraneousSubtypeEquiv system i : ExtraneousSubtype system) :
      Fin (basis system).length) = extraneousIndex i := by
  rfl

/-- The executable extraneous matrix is a reindexing of the actual principal
non-reduced block. -/
theorem extraneousMatrix_eq_submatrix_toSquareBlock {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    extraneousMatrix system =
      (Matrix.toSquareBlockProp (matrix system) (IsExtraneousIndex system)).submatrix
        (extraneousSubtypeEquiv system) (extraneousSubtypeEquiv system) := by
  ext i j
  rfl

/-- The computed extraneous factor is exactly the determinant of the
principal non-reduced block, independent of its executable list indexing. -/
theorem extraneousFactor_eq_det_toSquareBlock {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    extraneousFactor system =
      (Matrix.toSquareBlockProp (matrix system) (IsExtraneousIndex system)).det := by
  rw [extraneousFactor_eq_det, extraneousMatrix_eq_submatrix_toSquareBlock,
    Matrix.det_submatrix_equiv_self]

/-- Fraction field of the coefficient-polynomial ring. -/
abbrev ParameterFraction (n : ℕ) (F : Type*) [Field F] [BEq F] [LawfulBEq F] :=
  FractionRing (Parameters n F)

/-- The full Macaulay matrix embedded in the coefficient fraction field. -/
noncomputable def fractionMatrix {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Matrix (Fin (basis system).length) (Fin (basis system).length)
      (ParameterFraction n F) :=
  (algebraMap (Parameters n F) (ParameterFraction n F)).mapMatrix (matrix system)

/-- Principal non-reduced block over the coefficient fraction field. -/
noncomputable def fractionExtraneousBlock {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Matrix (ExtraneousSubtype system) (ExtraneousSubtype system)
      (ParameterFraction n F) :=
  Matrix.toSquareBlockProp (fractionMatrix system) (IsExtraneousIndex system)

/-- Complementary principal block over the coefficient fraction field. -/
noncomputable def fractionReducedBlock {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Matrix {i // ¬IsExtraneousIndex system i} {i // ¬IsExtraneousIndex system i}
      (ParameterFraction n F) :=
  Matrix.toSquareBlockProp (fractionMatrix system) fun i => ¬IsExtraneousIndex system i

/-- Rows in the non-reduced block and columns in its complement. -/
noncomputable def fractionUpperRightBlock {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Matrix (ExtraneousSubtype system) {i // ¬IsExtraneousIndex system i}
      (ParameterFraction n F) :=
  Matrix.toBlock (fractionMatrix system) (IsExtraneousIndex system)
    fun i => ¬IsExtraneousIndex system i

/-- Rows in the complementary block and columns in the non-reduced block. -/
noncomputable def fractionLowerLeftBlock {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Matrix {i // ¬IsExtraneousIndex system i} (ExtraneousSubtype system)
      (ParameterFraction n F) :=
  Matrix.toBlock (fractionMatrix system) (fun i => ¬IsExtraneousIndex system i)
    (IsExtraneousIndex system)

theorem toBlock_eq_fractionExtraneousBlock {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Matrix.toBlock (fractionMatrix system) (IsExtraneousIndex system)
      (IsExtraneousIndex system) = fractionExtraneousBlock system := rfl

theorem toBlock_eq_fractionUpperRightBlock {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Matrix.toBlock (fractionMatrix system) (IsExtraneousIndex system)
      (fun i => ¬IsExtraneousIndex system i) = fractionUpperRightBlock system := rfl

theorem toBlock_eq_fractionLowerLeftBlock {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Matrix.toBlock (fractionMatrix system) (fun i => ¬IsExtraneousIndex system i)
      (IsExtraneousIndex system) = fractionLowerLeftBlock system := rfl

theorem toBlock_eq_fractionReducedBlock {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Matrix.toBlock (fractionMatrix system) (fun i => ¬IsExtraneousIndex system i)
      (fun i => ¬IsExtraneousIndex system i) = fractionReducedBlock system := rfl

/-- Mapping the principal non-reduced determinant to the fraction field gives
the computed extraneous factor. -/
theorem det_fractionExtraneousBlock {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    (fractionExtraneousBlock system).det =
      algebraMap (Parameters n F) (ParameterFraction n F)
        (extraneousFactor system) := by
  rw [extraneousFactor_eq_det_toSquareBlock]
  change
    ((algebraMap (Parameters n F) (ParameterFraction n F)).mapMatrix
      (Matrix.toSquareBlockProp (matrix system) (IsExtraneousIndex system))).det = _
  rw [← RingHom.map_det]

/-- The fraction-field non-reduced block is invertible for every square input.
This uses the independently proved nonvanishing of the computed extraneous
determinant. -/
@[instance_reducible]
noncomputable def fractionExtraneousBlockInvertible {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Invertible (fractionExtraneousBlock system) := by
  have hdet : (fractionExtraneousBlock system).det ≠ 0 := by
    rw [det_fractionExtraneousBlock]
    simpa only [_root_.map_zero] using
      (IsFractionRing.injective (Parameters n F) (ParameterFraction n F)).ne
        (extraneousFactor_ne_zero system)
  letI : Invertible (fractionExtraneousBlock system).det := invertibleOfNonzero hdet
  exact Matrix.invertibleOfDetInvertible (fractionExtraneousBlock system)

/-- Schur complement of the computed non-reduced block after passing to the
coefficient fraction field. -/
noncomputable def fractionSchurComplement {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Matrix {i // ¬IsExtraneousIndex system i} {i // ¬IsExtraneousIndex system i}
      (ParameterFraction n F) :=
  fractionReducedBlock system -
    fractionLowerLeftBlock system * (fractionExtraneousBlock system)⁻¹ *
      fractionUpperRightBlock system

/-- The embedded full characteristic is the determinant of the full matrix
over the coefficient fraction field.  `Matrix.det_toBlock` supplies the
native non-reduced/reduced block decomposition of this determinant. -/
theorem fraction_characteristic_eq_det_fractionMatrix {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    algebraMap (Parameters n F) (ParameterFraction n F) (characteristic system) =
      (fractionMatrix system).det := by
  rw [characteristic_eq_det, RingHom.map_det]
  rfl

/-- The native block determinant factors through the non-reduced block and
its Schur complement.  Together with `fraction_characteristic_eq_det_fractionMatrix`,
and `det_fractionExtraneousBlock`, this reduces polynomial divisibility to
descent of the explicit Schur determinant. -/
theorem fraction_blockDet_eq_extraneousBlock_mul_schurDet {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    (Matrix.fromBlocks
      (fractionExtraneousBlock system)
      (fractionUpperRightBlock system)
      (fractionLowerLeftBlock system)
      (fractionReducedBlock system)).det =
      (fractionExtraneousBlock system).det *
        (fractionSchurComplement system).det := by
  have hfactor := @Matrix.det_fromBlocks₁₁
    (ExtraneousSubtype system) {i // ¬IsExtraneousIndex system i}
    (ParameterFraction n F) _ _ _ _ _
    (fractionExtraneousBlock system)
    (fractionUpperRightBlock system)
    (fractionLowerLeftBlock system)
    (fractionReducedBlock system)
    (fractionExtraneousBlockInvertible system)
  rw [@Matrix.invOf_eq_nonsing_inv _ _ _ _ _
    (fractionExtraneousBlock system)
    (fractionExtraneousBlockInvertible system)] at hfactor
  exact hfactor

end ArkLib.Rojas.Producer.MacaulayQuotient
