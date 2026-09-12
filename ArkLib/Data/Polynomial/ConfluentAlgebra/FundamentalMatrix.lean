/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.ConfluentAlgebra.SeriesNewton
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.NoncommRing

/-!
# Computed fundamental matrices

Matrix inversion and differential correction both execute precision doubling. All matrix
entries retain CompPoly's stored polynomial representation over the coefficient ring.
-/

@[expose] public section

namespace ArkLib.ConfluentAlgebra.FundamentalMatrix

open CompPoly ArkLib.TruncatedSeries

/-- Finite matrix data used by the recursive algorithms to retain computed entries. -/
abbrev MatrixData (R : Type*) (d : ℕ) := Vector (Vector R d) d

/-- Materialize every matrix entry. -/
def matrixData {R : Type*} {d : ℕ} (P : Matrix (Fin d) (Fin d) R) : MatrixData R d :=
  Vector.ofFn fun i => Vector.ofFn fun j => P i j

/-- Read a materialized matrix. -/
def dataMatrix {R : Type*} {d : ℕ} (P : MatrixData R d) : Matrix (Fin d) (Fin d) R :=
  fun i j => P[i.val][j.val]

@[simp] theorem dataMatrix_matrixData {R : Type*} {d : ℕ}
    (P : Matrix (Fin d) (Fin d) R) : dataMatrix (matrixData P) = P := by
  funext i j
  simp [dataMatrix, matrixData]

/-- Retain each inverse iterate as data, preventing recursive matrix-entry recomputation. -/
def inverseData {R : Type*} [Ring R] {d : ℕ} (a : MatrixData R d) : ℕ → MatrixData R d
  | 0 => matrixData 1
  | n + 1 =>
    matrixData (Polynomial.NewtonInverse.step (dataMatrix a) (dataMatrix (inverseData a n)))

/-- The stored inverse loop executes exactly the shared Newton updates. -/
theorem inverseData_eq {R : Type*} [Ring R] {d : ℕ} (a : MatrixData R d) (n : ℕ) :
    dataMatrix (inverseData a n) = Polynomial.NewtonInverse.iterate n (dataMatrix a) 1 := by
  induction n with
  | zero => simp only [inverseData, dataMatrix_matrixData, Polynomial.NewtonInverse.iterate]
  | succ n ih =>
    simp only [inverseData, dataMatrix_matrixData, ih, Polynomial.NewtonInverse.iterate]

variable {A : Type*} [CommRing A] [BEq A] [LawfulBEq A] [Nontrivial A]

/-- Square matrices of stored series. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) (CPolynomial A)

/-- Entrywise equality through a precision cap. -/
def LowEq (k : ℕ) {d : ℕ} (P Q : Mat (A := A) d) : Prop :=
  ∀ i j, TruncatedSeries.LowEq k (P i j) (Q i j)

/-- Entrywise vanishing order. -/
def Order (k : ℕ) {d : ℕ} (P : Mat (A := A) d) : Prop := LowEq k P 0

/-- Entrywise stored truncation. -/
def trunc (k : ℕ) {d : ℕ} (P : Mat (A := A) d) : Mat (A := A) d :=
  fun i j => truncate k (P i j)

/-- Projection to matrices over the stored truncated series ring. -/
def project (k d : ℕ) :
    Mat (A := A) d →+* Matrix (Fin d) (Fin d) (TruncatedSeries.Ring (A := A) k) :=
  (TruncatedSeries.project k).mapMatrix

@[simp] theorem project_apply (k d : ℕ) (P : Mat (A := A) d) (i j : Fin d) :
    project k d P i j = TruncatedSeries.project k (P i j) := rfl

/-- Equality after projection is precisely entrywise coefficient equality. -/
theorem project_eq_iff (k d : ℕ) (P Q : Mat (A := A) d) :
    project k d P = project k d Q ↔ LowEq k P Q := by
  constructor
  · intro he i j
    exact (TruncatedSeries.project_eq_iff k _ _).mp (congrFun (congrFun he i) j)
  · intro he
    funext i j
    exact (TruncatedSeries.project_eq_iff k _ _).mpr (he i j)

omit [BEq A] [LawfulBEq A] [Nontrivial A] in
theorem LowEq.refl (k : ℕ) {d : ℕ} (P : Mat (A := A) d) : LowEq k P P :=
  fun _ _ => TruncatedSeries.LowEq.refl _ _

omit [BEq A] [LawfulBEq A] [Nontrivial A] in
theorem LowEq.symm {k d : ℕ} {P Q : Mat (A := A) d} (h : LowEq k P Q) : LowEq k Q P :=
  fun i j => (h i j).symm

omit [BEq A] [LawfulBEq A] [Nontrivial A] in
theorem LowEq.trans {k d : ℕ} {P Q S : Mat (A := A) d}
    (h : LowEq k P Q) (h' : LowEq k Q S) : LowEq k P S := fun i j => (h i j).trans (h' i j)

omit [BEq A] [LawfulBEq A] [Nontrivial A] in
theorem LowEq.mono {k l d : ℕ} {P Q : Mat (A := A) d} (h : LowEq k P Q) (hl : l ≤ k) :
    LowEq l P Q := fun i j => (h i j).mono hl

omit [Nontrivial A] in
theorem LowEq.add {k d : ℕ} {P Q U V : Mat (A := A) d}
    (h : LowEq k P Q) (h' : LowEq k U V) : LowEq k (P + U) (Q + V) :=
  fun i j => (h i j).add (h' i j)

omit [Nontrivial A] in
theorem LowEq.sub {k d : ℕ} {P Q U V : Mat (A := A) d}
    (h : LowEq k P Q) (h' : LowEq k U V) : LowEq k (P - U) (Q - V) :=
  fun i j => (h i j).sub (h' i j)

theorem LowEq.mul {k d : ℕ} {P Q U V : Mat (A := A) d}
    (h : LowEq k P Q) (h' : LowEq k U V) : LowEq k (P * U) (Q * V) := by
  apply (project_eq_iff k d _ _).mp
  rw [map_mul, map_mul, (project_eq_iff k d _ _).mpr h,
    (project_eq_iff k d _ _).mpr h']

omit [Nontrivial A] in
theorem trunc_lowEq (k : ℕ) {d : ℕ} (P : Mat (A := A) d) : LowEq k (trunc k P) P := by
    intro i j
    exact truncate_lowEq k (P i j)

omit [BEq A] [LawfulBEq A] [Nontrivial A] in
theorem Order.zero (k d : ℕ) : Order k (0 : Mat (A := A) d) := LowEq.refl _ _

omit [BEq A] [LawfulBEq A] [Nontrivial A] in
theorem Order.of_zero {d : ℕ} (P : Mat (A := A) d) : Order 0 P := by
  intro i j n hn
  omega

omit [BEq A] [LawfulBEq A] [Nontrivial A] in
theorem Order.mono {k l d : ℕ} {P : Mat (A := A) d} (h : Order k P) (hl : l ≤ k) :
    Order l P := LowEq.mono h hl

/-- Matrix multiplication adds entrywise vanishing orders. -/
theorem Order.mul {m n d : ℕ} {P Q : Mat (A := A) d} (h : Order m P) (h' : Order n Q) :
    Order (m + n) (P * Q) := by
  intro i j
  have hs := TruncatedSeries.LowEq.sum Finset.univ
    (fun a _ => TruncatedSeries.Order.mul (h i a) (h' a j))
  simpa [Matrix.mul_apply] using hs

theorem Order.pow {m d : ℕ} {P : Mat (A := A) d} (h : Order m P) (n : ℕ) :
    Order (m * n) (P ^ n) := by
  induction n with
  | zero => exact Order.of_zero _
  | succ n ih => simpa [pow_succ, Nat.mul_succ] using ih.mul h

/-- Entrywise CompPoly differentiation. -/
def deriv {d : ℕ} (P : Mat (A := A) d) : Mat (A := A) d := fun i j => (P i j).derivative

/-- Differentiation of a stored polynomial as an additive homomorphism. -/
def derivHom : CPolynomial A →+ CPolynomial A where
  toFun := CPolynomial.derivative
  map_zero' := CPolynomial.derivative_zero
  map_add' p q := by
    apply CPolynomial.eq_iff_coeff.mpr
    intro i
    simp [CPolynomial.coeff_derivative, CPolynomial.coeff_add, add_mul]

theorem deriv_sub {d : ℕ} (P Q : Mat (A := A) d) : deriv (P - Q) = deriv P - deriv Q := by
  funext i j
  exact map_sub derivHom (P i j) (Q i j)

theorem deriv_mul {d : ℕ} (P Q : Mat (A := A) d) :
    deriv (P * Q) = deriv P * Q + P * deriv Q := by
  funext i j
  change derivHom (∑ a, P i a * Q a j) = _
  rw [map_sum]
  simp only [derivHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, CPolynomial.derivative_mul,
    Finset.sum_add_distrib, Matrix.add_apply, Matrix.mul_apply, deriv]

omit [Nontrivial A] in
theorem LowEq.deriv {k d : ℕ} {P Q : Mat (A := A) d} (h : LowEq k P Q) :
    LowEq (k - 1) (deriv P) (deriv Q) := fun i j => (h i j).rawDerivative

variable {E : Type*} [Field E]

/-- Entrywise zero-constant integration. -/
def integ (k : ℕ) (ι : E →+* A) {d : ℕ} (P : Mat (A := A) d) : Mat (A := A) d :=
  fun i j => integral k ι (P i j)

omit [Nontrivial A] in
theorem deriv_integ (p k : ℕ) [CharP E p] (ι : E →+* A) (hk : k ≤ p)
    {d : ℕ} (P : Mat (A := A) d) : LowEq (k - 1) (deriv (integ k ι P)) P := by
    intro i j
    exact rawDerivative_integral p k ι hk (P i j)

omit [Nontrivial A] in
theorem Order.integ {m k d : ℕ} {P : Mat (A := A) d} (h : Order m P) (ι : E →+* A) :
    Order (min k (m + 1)) (integ k ι P) := by
  intro i j
  exact TruncatedSeries.Order.integral (k := k) (h i j) ι

/-- Compute the inverse of a matrix whose constant term is the identity. -/
def inverse (k : ℕ) {d : ℕ} (P : Mat (A := A) d) : Mat (A := A) d :=
  let V := inverseData (matrixData (project k d P)) (Polynomial.NewtonInverse.rounds k)
  fun i j => (dataMatrix V i j).val

@[simp] theorem project_inverse (k : ℕ) {d : ℕ} (P : Mat (A := A) d) :
    project k d (inverse k P) = Polynomial.NewtonInverse.correct k (project k d P) 1 := by
  funext i j
  change TruncatedSeries.project k (inverse k P i j) = _
  have hV := inverseData_eq (matrixData (project k d P)) (Polynomial.NewtonInverse.rounds k)
  simp only [dataMatrix_matrixData] at hV
  simp only [inverse, hV]
  exact project_representative k _

/-- The computed inverse is valid through the requested cap. -/
theorem inverse_right (k : ℕ) {d : ℕ} (P : Mat (A := A) d) (hP : LowEq 1 P 1) :
    LowEq k (P * inverse k P) 1 := by
  have he : Order 1 (1 - P) := by
    intro i j n hn
    simp only [Matrix.sub_apply, CPolynomial.coeff_sub, hP i j n hn,
      Matrix.zero_apply, CPolynomial.coeff_zero, sub_self]
  have hp := he.pow k
  have hz : project k d ((1 - P) ^ k) = 0 := by
    rw [← map_zero (project k d)]
    apply (project_eq_iff k d _ _).mpr
    simpa only [Nat.one_mul, Order] using hp
  rw [map_pow, map_sub, map_one] at hz
  apply (project_eq_iff k d _ _).mp
  rw [map_mul, map_one, project_inverse]
  apply Polynomial.NewtonInverse.right_inverse
  simpa using hz

/-- The matrix inverse computed from the identity is also a left inverse. -/
theorem inverse_left (k : ℕ) {d : ℕ} (P : Mat (A := A) d) (hP : LowEq 1 P 1) :
    LowEq k (inverse k P * P) 1 := by
  let a := project k d P
  have hc : ∀ n, Commute a (Polynomial.NewtonInverse.iterate n a 1) := by
    intro n
    induction n with
    | zero => exact Commute.one_right a
    | succ n ih =>
      exact ih.mul_right ((Commute.ofNat_right a 2).sub_right ((Commute.refl a).mul_right ih))
  have hr := (project_eq_iff k d _ _).mpr (inverse_right k P hP)
  rw [map_mul, project_inverse, map_one] at hr
  apply (project_eq_iff k d _ _).mp
  rw [map_mul, project_inverse, map_one]
  change Polynomial.NewtonInverse.iterate (Polynomial.NewtonInverse.rounds k) a 1 * a = 1
  rw [← (hc (Polynomial.NewtonInverse.rounds k)).eq]
  exact hr

/-- The differential residual of a candidate fundamental matrix. -/
def residual {d : ℕ} (M P : Mat (A := A) d) : Mat (A := A) d := deriv P - M * P

/-- The actual fundamental-matrix Newton correction, with computed inverse and integral. -/
def step (k : ℕ) (ι : E →+* A) {d : ℕ} (M P : Mat (A := A) d) : Mat (A := A) d :=
  trunc k (P - P * integ k ι (inverse k P * residual M P))

/-- Exact algebraic identity behind the fundamental-matrix correction. -/
theorem residual_correction {d : ℕ} (M P J : Mat (A := A) d) :
    residual M (P - P * J) = residual M P - residual M P * J - P * deriv J := by
  simp only [residual, deriv_sub, deriv_mul]
  noncomm_ring

omit [BEq A] [LawfulBEq A] [Nontrivial A] in
/-- Entrywise vanishing transfers across equality at the required precision. -/
theorem LowEq.order {k d : ℕ} {P Q : Mat (A := A) d}
    (h : LowEq k P Q) (hq : Order k Q) : Order k P := h.trans hq

/-- Truncating the candidate only costs one coefficient in its differential residual. -/
theorem residual_trunc (k : ℕ) {d : ℕ} (M P : Mat (A := A) d) :
    LowEq (k - 1) (residual M (trunc k P)) (residual M P) :=
  (trunc_lowEq k P).deriv.sub
    ((LowEq.refl (k - 1) M).mul ((trunc_lowEq k P).mono (by omega)))

/-- One executed update doubles residual precision, with the derivative cap shown explicitly. -/
theorem step_precision (p k m : ℕ) [CharP E p] (ι : E →+* A) (hk : k ≤ p)
    {d : ℕ} (M P : Mat (A := A) d) (hP : LowEq 1 P 1)
    (hE : Order m (residual M P)) :
    Order (min (k - 1) (2 * m + 1)) (residual M (step k ι M P)) := by
  let B := inverse k P
  let U := residual M P
  let J := integ k ι (B * U)
  have hDJ := deriv_integ p k ι hk (B * U)
  have hPB := (inverse_right k P hP).mono (show k - 1 ≤ k by omega)
  have hcan : LowEq (k - 1) (P * deriv J) U := by
    have ht := (LowEq.refl (k - 1) P).mul hDJ
    have ht' := hPB.mul (LowEq.refl (k - 1) U)
    rw [mul_assoc] at ht'
    simpa only [one_mul] using ht.trans ht'
  have hr : LowEq (k - 1) (residual M (step k ι M P)) (-(U * J)) := by
    have ht := residual_trunc k M (P - P * J)
    rw [residual_correction] at ht
    have hc := ((LowEq.refl (k - 1) (U - U * J)).sub hcan)
    have heq : U - U * J - U = -(U * J) := by abel
    rw [heq] at hc
    exact ht.trans hc
  have hBU : Order m (B * U) := by
    simpa only [Nat.zero_add] using (Order.of_zero B).mul hE
  have hJ := hBU.integ (k := k) ι
  have hprod := hE.mul hJ
  have hbound : min (k - 1) (2 * m + 1) ≤ m + min k (m + 1) := by omega
  have hneg : Order (min (k - 1) (2 * m + 1)) (-(U * J)) := by
    intro i j
    exact TruncatedSeries.Order.neg ((hprod.mono hbound) i j)
  exact (hr.mono (Nat.min_le_left _ _)).order hneg

/-- The correction preserves the identity constant coefficient. -/
theorem step_initial (k : ℕ) (ι : E →+* A) (hk : 0 < k)
    {d : ℕ} (M P : Mat (A := A) d) (hP : LowEq 1 P 1) : LowEq 1 (step k ι M P) 1 := by
  have hJ := (Order.of_zero (inverse k P * residual M P)).integ (k := k) ι
  have hJ' : Order 1 (integ k ι (inverse k P * residual M P)) := by
    simpa only [Nat.zero_add, Nat.min_eq_right hk] using hJ
  have hPJ : Order 1 (P * integ k ι (inverse k P * residual M P)) := by
    simpa only [Nat.zero_add] using (Order.of_zero P).mul hJ'
  have ht := (LowEq.refl 1 P).sub hPJ
  simp only [sub_zero] at ht
  exact ((trunc_lowEq k _).mono hk).trans (ht.trans hP)

/-- Materialize the inverse, residual and integral once in a fundamental update. -/
def stepData (k : ℕ) (ι : E →+* A) {d : ℕ} (M : Mat (A := A) d)
    (values : MatrixData (CPolynomial A) d) : MatrixData (CPolynomial A) d :=
  let P := dataMatrix values
  let V := inverseData (matrixData (project k d P)) (Polynomial.NewtonInverse.rounds k)
  let B : Mat (A := A) d := fun i j => (dataMatrix V i j).val
  let U := matrixData (residual M P)
  let J := matrixData (integ k ι (B * dataMatrix U))
  matrixData (trunc k (P - P * dataMatrix J))

/-- The stored fundamental update is exactly the proved Newton formula. -/
theorem stepData_eq (k : ℕ) (ι : E →+* A) {d : ℕ} (M : Mat (A := A) d)
    (values : MatrixData (CPolynomial A) d) :
    dataMatrix (stepData k ι M values) = step k ι M (dataMatrix values) := by
  simp only [stepData, dataMatrix_matrixData, step, inverse]

/-- Store each fundamental iterate as finite data before the next Newton update. -/
def fundamentalData (k : ℕ) (ι : E →+* A) {d : ℕ} (M : Mat (A := A) d) :
    ℕ → MatrixData (CPolynomial A) d
  | 0 => matrixData 1
  | n + 1 => stepData k ι M (fundamentalData k ι M n)

/-- Execute the fundamental-matrix updates from the identity. -/
def iterate (k : ℕ) (ι : E →+* A) {d : ℕ} (M : Mat (A := A) d) (n : ℕ) :
    Mat (A := A) d := dataMatrix (fundamentalData k ι M n)

@[simp] theorem iterate_zero (k : ℕ) (ι : E →+* A) {d : ℕ} (M : Mat (A := A) d) :
    iterate k ι M 0 = 1 := dataMatrix_matrixData 1

/-- The materialized loop obeys exactly the proved fundamental-matrix update. -/
@[simp] theorem iterate_succ (k : ℕ) (ι : E →+* A) {d : ℕ} (M : Mat (A := A) d) (n : ℕ) :
    iterate k ι M (n + 1) = step k ι M (iterate k ι M n) :=
  stepData_eq k ι M _

/-- Every computed fundamental approximation has identity constant coefficient. -/
theorem iterate_initial (k : ℕ) (ι : E →+* A) (hk : 0 < k)
    {d : ℕ} (M : Mat (A := A) d) (n : ℕ) : LowEq 1 (iterate k ι M n) 1 := by
  induction n with
  | zero => rw [iterate_zero]; exact LowEq.refl _ _
  | succ n ih => rw [iterate_succ]; exact step_initial k ι hk M _ ih

/-- The executed round count tracks residual precision, including the initial constant matrix. -/
theorem iterate_precision (p k : ℕ) [CharP E p] (ι : E →+* A) (hk0 : 0 < k) (hk : k ≤ p)
    {d : ℕ} (M : Mat (A := A) d) (n : ℕ) :
    Order (min (k - 1) (2 ^ n - 1)) (residual M (iterate k ι M n)) := by
  induction n with
  | zero =>
    simpa only [iterate_zero, pow_zero, Nat.sub_self, Nat.min_zero]
      using Order.of_zero (residual M 1)
  | succ n ih =>
    have hs := step_precision p k (min (k - 1) (2 ^ n - 1)) ι hk M _
      (iterate_initial k ι hk0 M n) ih
    have he : min (k - 1) (2 * min (k - 1) (2 ^ n - 1) + 1) =
        min (k - 1) (2 ^ (n + 1) - 1) := by
      have hp : 0 < 2 ^ n := pow_pos (by decide) _
      rw [pow_succ]
      omega
    simpa only [he, iterate_succ] using hs

/-- Compute a fundamental matrix using the least sufficient number of doubling rounds. -/
def fundamental (k : ℕ) (ι : E →+* A) {d : ℕ} (M : Mat (A := A) d) : Mat (A := A) d :=
  iterate k ι M (Polynomial.NewtonInverse.rounds k)

theorem fundamental_initial (k : ℕ) (ι : E →+* A) (hk0 : 0 < k)
    {d : ℕ} (M : Mat (A := A) d) : LowEq 1 (fundamental k ι M) 1 :=
  iterate_initial k ι hk0 M _

/-- The computed matrix solves its differential equation through precision `k-1`. -/
theorem fundamental_precision (p k : ℕ) [CharP E p] (ι : E →+* A)
    (hk0 : 0 < k) (hk : k ≤ p) {d : ℕ} (M : Mat (A := A) d) :
    Order (k - 1) (residual M (fundamental k ι M)) := by
  have hs := iterate_precision p k ι hk0 hk M (Polynomial.NewtonInverse.rounds k)
  have hp := Polynomial.NewtonInverse.precision_le k
  simpa only [fundamental, Nat.min_eq_left
    (show k - 1 ≤ 2 ^ Polynomial.NewtonInverse.rounds k - 1 by omega)]
    using hs

/-- Public guarded fundamental-matrix producer. -/
def fundamental? (p k : ℕ) [CharP E p] (ι : E →+* A) {d : ℕ} (M : Mat (A := A) d) :
    Option (Mat (A := A) d) :=
  if 0 < k ∧ k ≤ p then
    let values := fundamentalData k ι M (Polynomial.NewtonInverse.rounds k)
    some (dataMatrix values)
  else none

/-- The guarded producer accepts exactly the supported integration range. -/
theorem fundamental?_eq_none_iff (p k : ℕ) [CharP E p] (ι : E →+* A) {d : ℕ} (M : Mat (A := A) d) :
    fundamental? p k ι M = none ↔ ¬ (0 < k ∧ k ≤ p) := by
  simp [fundamental?]

/-- Store all stages of variation of constants before reading any output entry. -/
def solutionData (k : ℕ) (ι : E →+* A) {d : ℕ} (M B : Mat (A := A) d) :
    MatrixData (CPolynomial A) d :=
  let values := fundamentalData k ι M (Polynomial.NewtonInverse.rounds k)
  let P := dataMatrix values
  let inverseValues := inverseData (matrixData (project k d P)) (Polynomial.NewtonInverse.rounds k)
  let V : Mat (A := A) d := fun i j => (dataMatrix inverseValues i j).val
  let J := matrixData (integ k ι (V * B))
  matrixData (trunc k (P * dataMatrix J))

/-- Variation of constants using a computed fundamental matrix and its computed inverse. -/
def solveZeroInitial (k : ℕ) (ι : E →+* A) {d : ℕ} (M B : Mat (A := A) d) : Mat (A := A) d :=
  dataMatrix (solutionData k ι M B)

/-- The stored inhomogeneous solver is exactly the fundamental-matrix formula. -/
theorem solveZeroInitial_eq (k : ℕ) (ι : E →+* A) {d : ℕ} (M B : Mat (A := A) d) :
    solveZeroInitial k ι M B =
      trunc k (fundamental k ι M * integ k ι (inverse k (fundamental k ι M) * B)) := by
  simp only [solveZeroInitial, solutionData, dataMatrix_matrixData, fundamental, iterate, inverse]

/-- The computed inhomogeneous solution has zero constant coefficient. -/
theorem solveZeroInitial_initial (k : ℕ) (ι : E →+* A) (hk0 : 0 < k)
    {d : ℕ} (M B : Mat (A := A) d) : Order 1 (solveZeroInitial k ι M B) := by
  rw [solveZeroInitial_eq]
  let P := fundamental k ι M
  have hJ := (Order.of_zero (inverse k P * B)).integ (k := k) ι
  have hprod := (Order.of_zero P).mul hJ
  have ht : Order 1 (P * integ k ι (inverse k P * B)) := by
    simpa only [Nat.zero_add, Nat.min_eq_right hk0] using hprod
  exact ((trunc_lowEq k _).mono hk0).order ht

/-- The fundamental-matrix formula solves the inhomogeneous equation at the derivative cap. -/
theorem solveZeroInitial_precision (p k : ℕ) [CharP E p] (ι : E →+* A)
    (hk0 : 0 < k) (hk : k ≤ p) {d : ℕ} (M B : Mat (A := A) d) :
    LowEq (k - 1) (residual M (solveZeroInitial k ι M B)) B := by
  rw [solveZeroInitial_eq]
  let P := fundamental k ι M
  let J := integ k ι (inverse k P * B)
  have hE := fundamental_precision p k ι hk0 hk M
  have hPB := (inverse_right k P (fundamental_initial k ι hk0 M)).mono
    (show k - 1 ≤ k by omega)
  have hDJ := deriv_integ p k ι hk (inverse k P * B)
  have hcan : LowEq (k - 1) (P * deriv J) B := by
    have ht := (LowEq.refl (k - 1) P).mul hDJ
    have ht' := hPB.mul (LowEq.refl (k - 1) B)
    rw [mul_assoc] at ht'
    simpa only [one_mul] using ht.trans ht'
  have heq : residual M (P * J) = residual M P * J + P * deriv J := by
    simp only [residual, deriv_mul]
    noncomm_ring
  have ht := residual_trunc k M (P * J)
  rw [heq] at ht
  have hz := LowEq.mul hE (LowEq.refl (k - 1) J)
  simp only [zero_mul] at hz
  have hs := hz.add hcan
  simp only [zero_add] at hs
  exact ht.trans hs

/-- Forcing order gives the first integration-order gain of the computed solution. -/
theorem solveZeroInitial_order (k m : ℕ) (ι : E →+* A)
    {d : ℕ} (M B : Mat (A := A) d) (hB : Order m B) :
    Order (min k (m + 1)) (solveZeroInitial k ι M B) := by
  rw [solveZeroInitial_eq]
  let P := fundamental k ι M
  have hIB : Order m (inverse k P * B) := by
    simpa only [Nat.zero_add] using (Order.of_zero (inverse k P)).mul hB
  have hJ := hIB.integ (k := k) ι
  have hPJ : Order (min k (m + 1)) (P * integ k ι (inverse k P * B)) := by
    simpa only [Nat.zero_add] using (Order.of_zero P).mul hJ
  exact ((trunc_lowEq k _).mono (Nat.min_le_left _ _)).order hPJ

/-- Hasse companion matrix for the normalized linearized equation. -/
def companion (d : ℕ) (V : CPolynomial A) (a : Fin (d + 1) → CPolynomial A) :
    Mat (A := A) d := fun i j =>
  if hn : i.val + 1 < d then
    if j = ⟨i.val + 1, hn⟩ then CPolynomial.C (i.val + 1 : A) else 0
  else -CPolynomial.C (d : A) * V * a j.castSucc

/-- The forcing occupies the last row and first column. -/
def companionForcing (d : ℕ) (V U : CPolynomial A) : Mat (A := A) d := fun i j =>
  if i.val + 1 = d ∧ j.val = 0 then -CPolynomial.C (d : A) * V * U else 0

/-- Compute the companion correction by the actual fundamental-matrix formula. -/
def companionSolution (k d : ℕ) (ι : E →+* A) (V U : CPolynomial A)
    (a : Fin (d + 1) → CPolynomial A) : Mat (A := A) d :=
  solveZeroInitial k ι (companion d V a) (companionForcing d V U)

/-- The computed companion matrix solves the displayed linearization. -/
theorem companionSolution_precision (p k d : ℕ) [CharP E p] (ι : E →+* A)
    (hk0 : 0 < k) (hk : k ≤ p) (V U : CPolynomial A)
    (a : Fin (d + 1) → CPolynomial A) :
    LowEq (k - 1) (residual (companion d V a) (companionSolution k d ι V U a))
      (companionForcing d V U) :=
  solveZeroInitial_precision p k ι hk0 hk _ _

/-- Every companion component has zero constant coefficient. -/
theorem companionSolution_initial (k d : ℕ) (ι : E →+* A) (hk0 : 0 < k)
    (V U : CPolynomial A) (a : Fin (d + 1) → CPolynomial A) :
    Order 1 (companionSolution k d ι V U a) := solveZeroInitial_initial k ι hk0 _ _

omit [Nontrivial A] in
/-- The forcing order is retained by normalization, without any field assumption on `A`. -/
theorem companionForcing_order (d m : ℕ) (V U : CPolynomial A)
    (hU : TruncatedSeries.Order m U) : Order m (companionForcing d V U) := by
  intro i j
  by_cases hi : i.val + 1 = d ∧ j.val = 0
  · simp only [companionForcing, if_pos hi]
    have hzero : TruncatedSeries.Order 0 (-CPolynomial.C (d : A) * V) := by
      intro n hn; omega
    simpa only [Nat.zero_add, TruncatedSeries.Order, Matrix.zero_apply] using hzero.mul hU
  · simp only [companionForcing, if_neg hi]
    exact TruncatedSeries.LowEq.refl _ _

/-- Generic integration-order guarantee for the computed companion correction. -/
theorem companionSolution_order (k d m : ℕ) (ι : E →+* A) (V U : CPolynomial A)
    (a : Fin (d + 1) → CPolynomial A) (hU : TruncatedSeries.Order m U) :
    Order (min k (m + 1)) (companionSolution k d ι V U a) :=
  solveZeroInitial_order k m ι _ _ (companionForcing_order d m V U hU)

/-- Each computed companion component is stored below the solution cap. -/
theorem companionSolution_degree (k d : ℕ) (ι : E →+* A) (V U : CPolynomial A)
    (a : Fin (d + 1) → CPolynomial A) (i j : Fin d) :
    (companionSolution k d ι V U a i j).toPoly.degree < k := by
  rw [companionSolution, solveZeroInitial_eq]
  exact degree_truncate_lt k _

/-- Each nonfinal companion row is the Hasse derivative-chain equation. -/
theorem companionSolution_row (p k d : ℕ) [CharP E p] (ι : E →+* A)
    (hk0 : 0 < k) (hk : k ≤ p) (V U : CPolynomial A)
    (a : Fin (d + 1) → CPolynomial A) (i : Fin d) (hn : i.val + 1 < d)
    (j : Fin d) :
    TruncatedSeries.LowEq (k - 1)
      (companionSolution k d ι V U a i j).derivative
      (CPolynomial.C (i.val + 1 : A) * companionSolution k d ι V U a ⟨i.val+1, hn⟩ j) := by
  have hs := companionSolution_precision p k d ι hk0 hk V U a i j
  have hne : ¬ (i.val + 1 = d ∧ j.val = 0) := by omega
  simp only [residual, deriv, Matrix.sub_apply, Matrix.mul_apply,
    companion, dif_pos hn, companionForcing, if_neg hne] at hs
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  exact TruncatedSeries.lowEq_iff_order_sub.mpr hs

/-- The final companion row is the normalized highest-derivative equation. -/
theorem companionSolution_last (p k d : ℕ) [CharP E p] (ι : E →+* A)
    (hk0 : 0 < k) (hk : k ≤ p) (hd : 0 < d) (V U : CPolynomial A)
    (a : Fin (d + 1) → CPolynomial A) :
    TruncatedSeries.LowEq (k - 1)
      ((companionSolution k d ι V U a ⟨d-1, by omega⟩ ⟨0, hd⟩).derivative +
        CPolynomial.C (d : A) * V *
          ∑ j, a j.castSucc * companionSolution k d ι V U a j ⟨0, hd⟩)
      (-CPolynomial.C (d : A) * V * U) := by
  have hs := companionSolution_precision p k d ι hk0 hk V U a
    ⟨d-1, by omega⟩ ⟨0, hd⟩
  have hlast : d - 1 + 1 = d := by omega
  simp only [residual, deriv, Matrix.sub_apply, Matrix.mul_apply, companion,
    companionForcing, hlast, Nat.lt_irrefl, ↓reduceDIte, and_self, if_true] at hs
  simpa only [neg_mul, mul_assoc, ← Finset.mul_sum, Finset.sum_neg_distrib,
    sub_neg_eq_add] using hs

section Nonlinear

variable [BEq E] [LawfulBEq E]
variable {r N : ℕ} [Fact (0 < N)]
variable (h : CPolynomial (CPoly.BoxAlgebra.Carrier r N E))
variable [Fact h.monic] [Fact (0 < h.toPoly.degree)]

/-- Compute the companion correction from the actual nonlinear equation and its partials. -/
def nonlinearCorrection? (k d : ℕ) (c : E) (T : CPoly.CMvPolynomial (d + 2) E)
    (Y : CPolynomial (Representative h)) : Option (CPolynomial (Representative h)) :=
  let a := SeriesNewton.jetPartial h k d c T Y
  let U := SeriesNewton.jetEval h k d c T Y
  (SeriesNewton.inverseSeries? h k (a ⟨d, by omega⟩)).map fun V =>
    if hd : 0 < d then
      companionSolution k d (SeriesNewton.scalarHom h) V U a ⟨0, hd⟩ ⟨0, hd⟩
    else -V * U

/-- One nonlinear Hasse-Newton update, using a computed fundamental-matrix correction. -/
def nonlinearStep? (k d : ℕ) (c : E) (T : CPoly.CMvPolynomial (d + 2) E)
    (Y : CPolynomial (Representative h)) : Option (CPolynomial (Representative h)) :=
  (nonlinearCorrection? h k d c T Y).map fun δ => truncate k (Y + δ)

/-- Execute precision-doubling nonlinear updates; no correction is supplied by the caller. -/
def nonlinearIterate? (k d : ℕ) (c : E) (T : CPoly.CMvPolynomial (d + 2) E) :
    ℕ → ℕ → CPolynomial (Representative h) → Option (CPolynomial (Representative h))
  | 0, _, Y => some Y
  | n + 1, m, Y =>
    (nonlinearStep? h (min (2 * m + d) k) d c T Y).bind
      (nonlinearIterate? k d c T n (2 * m))

/-- Build the initial polynomial from the chart's finite initial Hasse jet. -/
def initialPolynomial (d : ℕ) (jet : Fin (d + 1) → Representative h) :
    CPolynomial (Representative h) :=
  ofCoeffs (d + 1) (fun i => if hi : i < d + 1 then jet ⟨i, hi⟩ else 0)

omit [Fact (0 < h.toPoly.degree)] in
/-- The initial polynomial stores exactly the supplied Hasse jet. -/
@[simp] theorem initialPolynomial_coeff (d : ℕ)
    (jet : Fin (d + 1) → Representative h) (j : Fin (d + 1)) :
    (initialPolynomial h d jet).coeff j.val = jet j := by
  simp only [initialPolynomial, coeff_ofCoeffs, if_pos j.isLt, dif_pos j.isLt]

/-- At positive precision, the constant jet point is the supplied initial data. -/
theorem jetPoint_initialPolynomial_coeff_zero (k d : ℕ) (hk : 0 < k) (c : E)
    (jet : Fin (d + 1) → Representative h) (i : Fin (d + 2)) :
    (SeriesNewton.jetPoint h k d c (initialPolynomial h d jet) i).coeff 0 =
      Fin.cases (SeriesNewton.scalarHom h c) jet i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hx : (CPolynomial.X : CPolynomial (Representative h)).coeff 0 = 0 := by
      rw [CPolynomial.coeff_toPoly, CPolynomial.X_toPoly]
      simp
    simp [SeriesNewton.jetPoint, SeriesNewton.seriesScalarHom, CPolynomial.coeff_add,
      CPolynomial.coeff_C, hx]
  · simp [SeriesNewton.jetPoint, coeff_hasse, hk, initialPolynomial_coeff]

/-- Constant-coefficient evaluation recovers the geometric initial-jet equation.
No characteristic or integration bound is required. -/
theorem jetEval_initialPolynomial_coeff_zero (k d : ℕ) (hk : 0 < k) (c : E)
    (T : CPoly.CMvPolynomial (d + 2) E) (jet : Fin (d + 1) → Representative h) :
    (SeriesNewton.jetEval h k d c T (initialPolynomial h d jet)).coeff 0 =
      CPoly.CMvPolynomial.eval₂ (SeriesNewton.scalarHom h)
        (Fin.cases (SeriesNewton.scalarHom h c) jet) T := by
  let φ : CPolynomial (Representative h) →+* Representative h :=
    Polynomial.constantCoeff.comp CPolynomial.ringEquiv.toRingHom
  have hφ (q : CPolynomial (Representative h)) : φ q = q.coeff 0 := by
    simpa [φ, CPolynomial.ringEquiv_apply] using (CPolynomial.coeff_toPoly q 0).symm
  have hc : φ.comp (SeriesNewton.seriesScalarHom h) = SeriesNewton.scalarHom h := by
    apply RingHom.ext
    intro a
    change φ (SeriesNewton.seriesScalarHom h a) = _
    rw [hφ]
    simp [SeriesNewton.seriesScalarHom, CPolynomial.coeff_C]
  simp only [SeriesNewton.jetEval, CPoly.eval₂_equiv]
  rw [← hφ, MvPolynomial.hom_eval₂, hc]
  congr 1
  funext i
  exact (hφ _).trans (jetPoint_initialPolynomial_coeff_zero h k d hk c jet i)

/-- The same specialization bridge applies to every stored jet partial, including the highest. -/
theorem jetPartial_initialPolynomial_coeff_zero (k d : ℕ) (hk : 0 < k) (c : E)
    (T : CPoly.CMvPolynomial (d + 2) E) (jet : Fin (d + 1) → Representative h)
    (j : Fin (d + 1)) :
    (SeriesNewton.jetPartial h k d c T (initialPolynomial h d jet) j).coeff 0 =
      CPoly.CMvPolynomial.eval₂ (SeriesNewton.scalarHom h)
        (Fin.cases (SeriesNewton.scalarHom h c) jet)
        (CPoly.CMvPolynomial.partialDerivative ⟨j.val + 1, by omega⟩ T) :=
  jetEval_initialPolynomial_coeff_zero h k d hk c _ jet

/-- Full guarded nonlinear series producer from initial jet data.

The solution is stored through `k`; the differential residual target is separately `k-d`.
-/
def nonlinearNewton? (p k d : ℕ) [CharP E p] (c : E) (T : CPoly.CMvPolynomial (d + 2) E)
    (jet : Fin (d + 1) → Representative h) : Option (CPolynomial (Representative h)) :=
  if d < k ∧ k ≤ p then
    let Y := initialPolynomial h d jet
    if (SeriesNewton.jetEval h k d c T Y).coeff 0 == 0 then
      (inverse? h ((SeriesNewton.jetPartial h k d c T Y ⟨d, by omega⟩).coeff 0)).bind
        fun _ => nonlinearIterate? h k d c T (Polynomial.NewtonInverse.rounds (k - d)) 1 Y
    else none
  else none

/-- Unsupported characteristic/precision inputs are rejected before integration. -/
theorem nonlinearNewton?_unsupported (p k d : ℕ) [CharP E p] (c : E)
    (T : CPoly.CMvPolynomial (d + 2) E) (jet : Fin (d + 1) → Representative h)
    (hg : ¬ (d < k ∧ k ≤ p)) : nonlinearNewton? h p k d c T jet = none := by
  simp only [nonlinearNewton?, if_neg hg]

/-- Every nonlinear update stores only coefficients below its active cap. -/
theorem nonlinearStep?_degree (k d : ℕ) (c : E) (T : CPoly.CMvPolynomial (d + 2) E)
    (Y Z : CPolynomial (Representative h)) (hZ : nonlinearStep? h k d c T Y = some Z) :
    Z.toPoly.degree < k := by
  obtain ⟨δ, _, rfl⟩ := Option.map_eq_some_iff.mp hZ
  exact degree_truncate_lt k _

/-- Clipped iteration never exceeds its requested solution cap. -/
theorem nonlinearIterate?_degree (k d : ℕ) (c : E) (T : CPoly.CMvPolynomial (d + 2) E)
    (n m : ℕ) (Y Z : CPolynomial (Representative h)) (hY : Y.toPoly.degree < k)
    (hZ : nonlinearIterate? h k d c T n m Y = some Z) : Z.toPoly.degree < k := by
  induction n generalizing m Y with
  | zero =>
    simp only [nonlinearIterate?, Option.some.injEq] at hZ
    subst Z
    exact hY
  | succ n ih =>
    obtain ⟨W, hW, hZ⟩ := Option.bind_eq_some_iff.mp hZ
    apply ih (2 * m) W ?_ hZ
    exact lt_of_lt_of_le (nonlinearStep?_degree h _ d c T Y W hW)
      (by exact_mod_cast Nat.min_le_right (2 * m + d) k)

omit [Fact (0 < h.toPoly.degree)] in
/-- The finite chart jet is stored below degree `d+1`. -/
theorem initialPolynomial_degree (d : ℕ) (jet : Fin (d + 1) → Representative h) :
    (initialPolynomial h d jet).toPoly.degree < (d + 1 : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro i hi
  rw [← CPolynomial.coeff_toPoly]
  simp only [initialPolynomial, coeff_ofCoeffs, if_neg (Nat.not_lt.mpr hi)]

/-- A successful public producer has exactly the requested stored solution degree bound. -/
theorem nonlinearNewton?_degree (p k d : ℕ) [CharP E p] (c : E)
    (T : CPoly.CMvPolynomial (d + 2) E)
    (jet : Fin (d + 1) → Representative h) (Y : CPolynomial (Representative h))
    (hY : nonlinearNewton? h p k d c T jet = some Y) : Y.toPoly.degree < k := by
  dsimp only [nonlinearNewton?] at hY
  split_ifs at hY with hg hr
  · obtain ⟨v, _, hv⟩ := Option.bind_eq_some_iff.mp hY
    apply nonlinearIterate?_degree h k d c T _ _ _ Y ?_ hv
    exact lt_of_lt_of_le (initialPolynomial_degree h d jet)
      (by exact_mod_cast (show d + 1 ≤ k by omega))

/-- Successful initialization certifies the guard, initial root, and computed separant inverse. -/
theorem nonlinearNewton?_initialCertificate (p k d : ℕ) [CharP E p] (c : E)
    (T : CPoly.CMvPolynomial (d + 2) E) (jet : Fin (d + 1) → Representative h)
    (Y : CPolynomial (Representative h)) (hY : nonlinearNewton? h p k d c T jet = some Y) :
    (d < k ∧ k ≤ p) ∧
    (SeriesNewton.jetEval h k d c T (initialPolynomial h d jet)).coeff 0 = 0 ∧
    ∃ v, inverse? h ((SeriesNewton.jetPartial h k d c T
      (initialPolynomial h d jet) ⟨d, by omega⟩).coeff 0) = some v := by
  dsimp only [nonlinearNewton?] at hY
  split_ifs at hY with hg hr
  · obtain ⟨v, hv, _⟩ := Option.bind_eq_some_iff.mp hY
    exact ⟨hg, by simpa only [beq_iff_eq] using hr, v, hv⟩

end Nonlinear

end ArkLib.ConfluentAlgebra.FundamentalMatrix
