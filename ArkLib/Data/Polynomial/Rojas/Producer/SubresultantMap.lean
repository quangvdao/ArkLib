/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.SpecializationFamily
public import ArkLib.Data.Polynomial.UnivariateRepresentation.Point
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Rojas Steps 4--5: first subresultants and a rational coordinate map

This module consumes an actual `SpecializationCandidate`.  It squarefree-reduces the base and
shifted eliminants, performs the paper's affine substitution
`q⁺((α + 1)θ - αt)`, computes the two prescribed maximal minors, and reduces both minors modulo
the base eliminant.  The per-coordinate denominators are combined into the single denominator
required by `UnivariateRepresentation.MapData`.

The rectangular matrix follows Rojas, *Solving Degenerate Sparse Polynomial Systems Faster*,
Section 5.1, page 20: there are `d₁ - 1` shifted rows from the second polynomial and `d₂ - 1`
shifted rows from the first.  We store coefficients in increasing degree order, so the constant
and linear output columns are the first two columns.  The deleted-minor pair is named by its
semantic role: `R₁ + R₀ t` is the linear subresultant, and Step 5 computes `-θ - R₁/R₀`.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.SubresultantMap

open CompPoly CompPoly.CPolynomial
open ArkLib.UnivariateRepresentation

variable {F : Type*} [Field F] [Fintype F] [BEq F] [LawfulBEq F]
variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Number of rows in the first-subresultant matrix. -/
def firstSubresultantSize {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]
    (f g : CPolynomial R) : ℕ :=
  f.natDegree + g.natDegree - 2

/-- The rectangular coefficient matrix from Rojas's definition of the first subresultant.
Coefficients are stored in increasing degree order, exactly as displayed in the source. -/
def firstSubresultantMatrix {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]
    (f g : CPolynomial R) :
    Matrix (Fin (firstSubresultantSize f g)) (Fin (firstSubresultantSize f g + 1)) R :=
  Matrix.of fun row column ↦
    let d₁ := f.natDegree
    let d₂ := g.natDegree
    if _hβ : row.val < d₁ - 1 then
      if _hleft : row.val ≤ column.val then
        if column.val ≤ row.val + d₂ then g.coeff (column.val - row.val) else 0
      else 0
    else
      let shift := row.val - (d₁ - 1)
      if _hleft : shift ≤ column.val then
        if column.val ≤ shift + d₁ then f.coeff (column.val - shift) else 0
      else 0

/-- Delete one column from a rectangular `k × (k+1)` matrix. -/
def minorOmitting {R : Type*} [CommRing R] {k : ℕ}
    (matrix : Matrix (Fin k) (Fin (k + 1)) R) (omitted : Fin (k + 1)) :
    Matrix (Fin k) (Fin k) R :=
  Matrix.of fun i j ↦ matrix i (omitted.succAbove j)

/-- The paper's two first-subresultant coefficients `(R₀, R₁)`.

When both inputs are linear, the displayed deleted-minor matrix has no second-to-last column.
In that case `f = a₀ + a₁t` already gives the needed Step-5 ratio, so the executable convention is
`(R₀, R₁) = (a₁, a₀)`.  Under the specialization guard, `a₁` is nonzero. -/
def firstSubresultant {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]
    (f g : CPolynomial R) : R × R :=
  let k := firstSubresultantSize f g
  let matrix := firstSubresultantMatrix f g
  if hk : k = 0 then (f.coeff 1, f.coeff 0)
  else
    let constantColumn : Fin (k + 1) := ⟨0, by omega⟩
    let linearColumn : Fin (k + 1) := ⟨1, by omega⟩
    let r₀ := (minorOmitting matrix constantColumn).det
    let r₁ := (minorOmitting matrix linearColumn).det
    (r₀, r₁)

theorem firstSubresultant_of_natDegree_eq_one
    {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]
    (f g : CPolynomial R) (hf : f.natDegree = 1) (hg : g.natDegree = 1) :
    firstSubresultant f g = (f.coeff 1, f.coeff 0) := by
  simp [firstSubresultant, firstSubresultantSize, hf, hg]

theorem firstSubresultant_linear_denominator_ne_zero
    {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]
    (f g : CPolynomial R) (hf : f.natDegree = 1) (hg : g.natDegree = 1) :
    (firstSubresultant f g).1 ≠ 0 := by
  rw [firstSubresultant_of_natDegree_eq_one f g hf hg]
  have hfne : f ≠ 0 := by
    intro hzero
    have hfpoly : f.toPoly.natDegree = 1 := by
      simpa only [← CPolynomial.natDegree_toPoly] using hf
    rw [hzero, CPolynomial.toPoly_zero, Polynomial.natDegree_zero] at hfpoly
    omega
  have hlead := CPolynomial.leadingCoeff_ne_zero hfne
  rw [CPolynomial.leadingCoeff_eq_coeff_natDegree, hf] at hlead
  exact hlead

/-- Regard an `F[t]` polynomial as a polynomial in `t` over `F[θ]`. -/
def liftInTheta (q : CPolynomial F) : CPolynomial (CPolynomial F) :=
  q.eval₂ (CHom.comp CHom) X

/-- The Step-4 affine substitution `q((α + 1)θ - αt)`, stored as an element of `F[θ][t]`. -/
def affineTransform (α : F) (q : CPolynomial F) : CPolynomial (CPolynomial F) :=
  q.eval₂ (CHom.comp CHom)
    (C (C (α + 1) * X) - C (C α) * X)

/-- The squarefree Step-1 eliminant. -/
def modulus (candidate : SpecializationCandidate (F := F)) : CPolynomial F :=
  squarefreeSupport p candidate.eliminant

/-- The squarefree Step-2 polynomial for coordinate `i`. -/
def minusPolynomial (dimension : ℕ) (candidate : SpecializationCandidate (F := F))
    (i : Fin dimension) : CPolynomial F :=
  squarefreeSupport p (candidate.shiftedEliminants[i.val]?.getD 0)

/-- The squarefree Step-3 polynomial for coordinate `i`; plus polynomials follow all minus
polynomials in `SpecializationCandidate.shiftedEliminants`. -/
def plusPolynomial (dimension : ℕ) (candidate : SpecializationCandidate (F := F))
    (i : Fin dimension) : CPolynomial F :=
  squarefreeSupport p (candidate.shiftedEliminants[dimension + i.val]?.getD 0)

/-- Unreduced Step-4 determinants for one coordinate. -/
def coordinateSubresultant (dimension : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) (i : Fin dimension) :
    CPolynomial F × CPolynomial F :=
  firstSubresultant
    (liftInTheta (minusPolynomial p dimension candidate i))
    (affineTransform α (plusPolynomial p dimension candidate i))

/-- Step-4 determinants reduced modulo the squarefree base eliminant. -/
def reducedCoordinateSubresultant (dimension : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) (i : Fin dimension) :
    CPolynomial F × CPolynomial F :=
  let result := coordinateSubresultant p dimension α candidate i
  (result.1.modByMonic (modulus p candidate),
    result.2.modByMonic (modulus p candidate))

/-- The product of all reduced `rᵢ,₀` before the final modulus reduction. -/
def rawCommonDenominator (dimension : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) : CPolynomial F :=
  ∏ i : Fin dimension, (reducedCoordinateSubresultant p dimension α candidate i).1

/-- The common rational denominator reduced modulo the Step-1 eliminant. -/
def commonDenominator (dimension : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) : CPolynomial F :=
  (rawCommonDenominator p dimension α candidate).modByMonic (modulus p candidate)

/-- The numerator for coordinate `i` before its final modulus reduction. -/
def rawCoordinateNumerator (dimension : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) (i : Fin dimension) : CPolynomial F :=
  let result := reducedCoordinateSubresultant p dimension α candidate i
  let others := (Finset.univ.erase i).prod
    (fun j ↦ (reducedCoordinateSubresultant p dimension α candidate j).1)
  (-1) * (X * result.1 + result.2) * others

/-- The Step-5 numerator for coordinate `i`, reduced modulo `h`.  Dividing by
`commonDenominator` gives `-θ - rᵢ,₁/rᵢ,₀`. -/
def coordinateNumerator (dimension : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) (i : Fin dimension) : CPolynomial F :=
  (rawCoordinateNumerator p dimension α candidate i).modByMonic (modulus p candidate)

/-- Executable Steps 4--5 output in the existing rational-univariate-map format. -/
def produce (dimension : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) : MapData (F := F) :=
  { modulus := modulus p candidate
    denominator := commonDenominator p dimension α candidate
    numerators := List.ofFn (coordinateNumerator p dimension α candidate) }

omit [Fact (Nat.Prime p)] [CharP F p] in
@[simp]
theorem produce_modulus (dimension : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) :
    (produce p dimension α candidate).modulus = modulus p candidate := rfl

omit [Fact (Nat.Prime p)] [CharP F p] in
@[simp]
theorem produce_denominator (dimension : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) :
    (produce p dimension α candidate).denominator =
      commonDenominator p dimension α candidate := rfl

omit [Fact (Nat.Prime p)] [CharP F p] in
@[simp]
theorem produce_numerators_length (dimension : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) :
    (produce p dimension α candidate).numerators.length = dimension := by
  simp [produce]

noncomputable section

variable {K : Type*} [Field K]

local instance : DecidableEq K := Classical.decEq K

/-- Evaluate a stored `F[θ]` coefficient after embedding `F` into an extension field. -/
def coefficientEval (ι : F →+* K) (θ : K) : CPolynomial F →+* K :=
  (Polynomial.eval₂RingHom ι θ).comp CPolynomial.toPolyRingHom

omit [Fintype F] in
@[simp]
theorem coefficientEval_apply (ι : F →+* K) (θ : K) (q : CPolynomial F) :
    coefficientEval ι θ q = q.toPoly.eval₂ ι θ := by
  simp [coefficientEval, RingHom.comp_apply]

/-- Evaluate a stored `F[θ][t]` polynomial first at `θ`, leaving a mathematical polynomial in
the outer variable `t`. -/
def specializeTheta (ι : F →+* K) (θ : K)
    (q : CPolynomial (CPolynomial F)) : Polynomial K :=
  q.toPoly.map (coefficientEval ι θ)

omit [Fintype F] in
/-- Exact two-variable meaning of the executable affine substitution.  In particular the inner
stored variable is sent to `θ`, while the outer stored variable is independently sent to `t`. -/
theorem affineTransform_eval₂ (ι : F →+* K) (θ t : K) (α : F)
    (q : CPolynomial F) :
    (affineTransform α q).toPoly.eval₂ (coefficientEval ι θ) t =
      q.toPoly.eval₂ ι ((ι α + 1) * θ - ι α * t) := by
  let outerEval : CPolynomial (CPolynomial F) →+* K :=
    (Polynomial.eval₂RingHom (coefficientEval ι θ) t).comp CPolynomial.toPolyRingHom
  calc
    _ = outerEval (affineTransform α q) := by
      simp [outerEval, RingHom.comp_apply]
    _ = outerEval
        (q.toPoly.eval₂ (CHom.comp CHom)
          (C (C (α + 1) * X) - C (C α) * X)) := by
      rw [affineTransform, CPolynomial.eval₂_toPoly]
    _ = _ := by
      rw [Polynomial.hom_eval₂]
      congr 1
      · ext a
        simp [outerEval, coefficientEval, RingHom.comp_apply,
          CPolynomial.C_toPoly]
      · simp [outerEval, coefficientEval, RingHom.comp_apply,
          CPolynomial.C_toPoly, CPolynomial.X_toPoly, CPolynomial.toPoly_mul,
          CPolynomial.toPoly_sub]

/-- Proof-facing Step-4 hypothesis at one root.  It says that the computed linear first
subresultant is a nonzero scalar multiple of the monic evaluated gcd, and that the gcd's common
root is the shifted coordinate `θ + point i`.  The scalar is necessary: determinant
subresultants are only associated to the normalized Euclidean gcd.  This is the precise
conditional form of the classical subresultant fact used in Rojas Section 5.1. -/
structure GcdLinearAtRoot (dimension : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) (ι : F →+* K)
    (θ : K) (point : Fin dimension → K) : Prop where
  candidate_nonzero : candidate.eliminant ≠ 0
  modulus_root : (modulus p candidate).toPoly.eval₂ ι θ = 0
  denominator_ne_zero : ∀ i : Fin dimension,
    coefficientEval ι θ
      (reducedCoordinateSubresultant p dimension α candidate i).1 ≠ 0
  associated_gcd : ∀ i : Fin dimension, ∃ scale : K, scale ≠ 0 ∧
    Polynomial.C (coefficientEval ι θ
          (reducedCoordinateSubresultant p dimension α candidate i).2) +
        Polynomial.C (coefficientEval ι θ
          (reducedCoordinateSubresultant p dimension α candidate i).1) * Polynomial.X =
      Polynomial.C scale *
        EuclideanDomain.gcd
          (specializeTheta ι θ
            (liftInTheta (minusPolynomial p dimension candidate i)))
          (specializeTheta ι θ
            (affineTransform α (plusPolynomial p dimension candidate i)))
  common_root : ∀ i : Fin dimension,
    (EuclideanDomain.gcd
        (specializeTheta ι θ
          (liftInTheta (minusPolynomial p dimension candidate i)))
        (specializeTheta ι θ
          (affineTransform α (plusPolynomial p dimension candidate i)))).eval
        (θ + point i) = 0

theorem GcdLinearAtRoot.modulus_monic
    {dimension : ℕ} {α : F} {candidate : SpecializationCandidate (F := F)}
    {ι : F →+* K} {θ : K} {point : Fin dimension → K}
    (hypotheses : GcdLinearAtRoot p dimension α candidate ι θ point) :
    (modulus p candidate).toPoly.Monic :=
  (CPolynomial.monic_toPoly_iff _).mp
    (CPolynomial.squarefreeSupport_monic p hypotheses.candidate_nonzero)

theorem coefficientEval_modByModulus
    {candidate : SpecializationCandidate (F := F)} {ι : F →+* K} {θ : K}
    (hcandidate : candidate.eliminant ≠ 0)
    (hroot : (modulus p candidate).toPoly.eval₂ ι θ = 0)
    (q : CPolynomial F) :
    coefficientEval ι θ (q.modByMonic (modulus p candidate)) = coefficientEval ι θ q := by
  rw [coefficientEval_apply, coefficientEval_apply,
    CPolynomial.toPoly_modByMonic q (modulus p candidate)
      ((CPolynomial.monic_toPoly_iff _).mp
        (CPolynomial.squarefreeSupport_monic p hcandidate)),
    Polynomial.eval₂_modByMonic_eq_self_of_root hroot]

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem GcdLinearAtRoot.coefficient_relation
    {dimension : ℕ} {α : F} {candidate : SpecializationCandidate (F := F)}
    {ι : F →+* K} {θ : K} {point : Fin dimension → K}
    (hypotheses : GcdLinearAtRoot p dimension α candidate ι θ point)
    (i : Fin dimension) :
    coefficientEval ι θ
        (reducedCoordinateSubresultant p dimension α candidate i).2 +
      coefficientEval ι θ
          (reducedCoordinateSubresultant p dimension α candidate i).1 *
        (θ + point i) = 0 := by
  obtain ⟨scale, _hscale, hassociated⟩ := hypotheses.associated_gcd i
  have heval := congrArg (Polynomial.eval (θ + point i)) hassociated
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at heval
  rw [hypotheses.common_root i] at heval
  simpa using heval

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- The computed Step-4 coefficient ratio is the negative shifted coordinate. -/
theorem GcdLinearAtRoot.subresultant_ratio
    {dimension : ℕ} {α : F} {candidate : SpecializationCandidate (F := F)}
    {ι : F →+* K} {θ : K} {point : Fin dimension → K}
    (hypotheses : GcdLinearAtRoot p dimension α candidate ι θ point)
    (i : Fin dimension) :
    coefficientEval ι θ
          (reducedCoordinateSubresultant p dimension α candidate i).2 /
        coefficientEval ι θ
          (reducedCoordinateSubresultant p dimension α candidate i).1 =
      -(θ + point i) := by
  have hrelation := GcdLinearAtRoot.coefficient_relation (p := p) hypotheses i
  have hne := hypotheses.denominator_ne_zero i
  field_simp
  linear_combination hrelation

theorem coefficientEval_commonDenominator
    (dimension : ℕ) (α : F) (candidate : SpecializationCandidate (F := F))
    (ι : F →+* K) (θ : K) (hcandidate : candidate.eliminant ≠ 0)
    (hroot : (modulus p candidate).toPoly.eval₂ ι θ = 0) :
    coefficientEval ι θ (commonDenominator p dimension α candidate) =
      ∏ i : Fin dimension,
        coefficientEval ι θ
          (reducedCoordinateSubresultant p dimension α candidate i).1 := by
  rw [commonDenominator,
    coefficientEval_modByModulus p hcandidate hroot]
  simp [rawCommonDenominator]

theorem coefficientEval_coordinateNumerator
    (dimension : ℕ) (α : F) (candidate : SpecializationCandidate (F := F))
    (ι : F →+* K) (θ : K) (i : Fin dimension)
    (hcandidate : candidate.eliminant ≠ 0)
    (hroot : (modulus p candidate).toPoly.eval₂ ι θ = 0) :
    coefficientEval ι θ (coordinateNumerator p dimension α candidate i) =
      (-1) *
        (θ * coefficientEval ι θ
            (reducedCoordinateSubresultant p dimension α candidate i).1 +
          coefficientEval ι θ
            (reducedCoordinateSubresultant p dimension α candidate i).2) *
        ∏ j ∈ Finset.univ.erase i,
          coefficientEval ι θ
            (reducedCoordinateSubresultant p dimension α candidate j).1 := by
  rw [coordinateNumerator,
    coefficientEval_modByModulus p hcandidate hroot]
  simp only [rawCoordinateNumerator]
  simp only [map_mul, map_add, map_one, map_neg, map_prod]
  rw [coefficientEval_apply, CPolynomial.X_toPoly, Polynomial.eval₂_X]

/-- Rojas Steps 4--5 represent every root satisfying the explicit linear-gcd hypotheses. -/
theorem produce_representsPoint
    {dimension : ℕ} {α : F} {candidate : SpecializationCandidate (F := F)}
    {ι : F →+* K} {θ : K} {point : Fin dimension → K}
    (hypotheses : GcdLinearAtRoot p dimension α candidate ι θ point) :
    (produce p dimension α candidate).RepresentsPoint ι θ point := by
  refine ⟨hypotheses.modulus_root, ?_, by simp [produce], ?_⟩
  · rw [show (produce p dimension α candidate).denominator =
      commonDenominator p dimension α candidate from rfl]
    rw [← coefficientEval_apply]
    rw [coefficientEval_commonDenominator (p := p) dimension α candidate ι θ
      hypotheses.candidate_nonzero hypotheses.modulus_root]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hypotheses.denominator_ne_zero i
  · intro i
    simp only [produce, List.getElem?_ofFn]
    have hget :
        (if h : i.val < dimension then
            some (coordinateNumerator p dimension α candidate ⟨i.val, h⟩)
          else none).getD 0 =
        coordinateNumerator p dimension α candidate i := by
      simp [i.isLt]
    rw [hget, ← coefficientEval_apply, ← coefficientEval_apply]
    rw [coefficientEval_coordinateNumerator (p := p) dimension α candidate ι θ i
        hypotheses.candidate_nonzero hypotheses.modulus_root,
      coefficientEval_commonDenominator (p := p) dimension α candidate ι θ
        hypotheses.candidate_nonzero hypotheses.modulus_root]
    let a : Fin dimension → K := fun j ↦ coefficientEval ι θ
      (reducedCoordinateSubresultant p dimension α candidate j).1
    let b : Fin dimension → K := fun j ↦ coefficientEval ι θ
      (reducedCoordinateSubresultant p dimension α candidate j).2
    have hrelation : b i + a i * (θ + point i) = 0 :=
      GcdLinearAtRoot.coefficient_relation (p := p) hypotheses i
    have hfactor : (-1) * (θ * a i + b i) = a i * point i := by
      linear_combination -hrelation
    have hprod : a i * ∏ j ∈ Finset.univ.erase i, a j = ∏ j, a j := by
      exact Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)
    have hdenominator : (∏ j, a j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ ↦ hypotheses.denominator_ne_zero j
    change ((-1) * (θ * a i + b i) * ∏ j ∈ Finset.univ.erase i, a j) /
        (∏ j, a j) = point i
    rw [hfactor]
    rw [show a i * point i * (∏ j ∈ Finset.univ.erase i, a j) =
      point i * (a i * ∏ j ∈ Finset.univ.erase i, a j) by ring, hprod]
    exact mul_div_cancel_right₀ (point i) hdenominator

end

end ArkLib.Rojas.Producer.SubresultantMap
