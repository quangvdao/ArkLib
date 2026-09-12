/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.Source
public import ArkLib.ToCompPoly.Multivariate.Eval
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Executable dense Macaulay determinant for square systems

This file constructs the square Macaulay matrix for

`Res(F - s FStar, u₀ + u₁x₁ + ... + uₙxₙ)`

directly from a computable square system.  The dense perturbation is the one
fixed in Rojas, Section 3.4: `FStarᵢ = xᵢ^dᵢ`.  Rows and columns are indexed by
weak compositions of Macaulay degree `1 + Σᵢ (dᵢ - 1)`.  A row indexed by `a`
is assigned to the first paired leading power dividing `x^a` and stores the
coefficients of the corresponding monomial multiple of that equation.

The matrix coefficients are computable polynomials in `(u₀,...,uₙ,s)`.  Thus
sparse supports, degree envelopes, the Macaulay determinant, and its lowest
nonzero `s`-coefficient are all derived from the input equations.  For general
degrees the determinant is a resultant multiple; identifying and dividing its
extraneous factor is deliberately not asserted here.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.DenseMacaulay

open CPoly CPoly.CMvPolynomial

variable {F : Type*} [CommRing F] [BEq F] [LawfulBEq F]

/-- Coefficient polynomials in `(u₀,...,uₙ,s)`, with `s` last. -/
abbrev Parameters (n : ℕ) (F : Type*) [Zero F] := CMvPolynomial (n + 2) F

/-- Sparse support copied from the executable input representation. -/
def sparseSupport {n : ℕ} (f : CMvPolynomial n F) : List (CMvMonomial n) :=
  f.monomials

/-- Positive dense degree envelope.  Constants and zero receive degree one,
so degenerate systems retain an explicit characteristic matrix. -/
def denseDegree {n : ℕ} (f : CMvPolynomial n F) : ℕ := max 1 f.totalDegree

/-- All weak compositions of `degree` into `count` parts. -/
def weakCompositions : (count degree : ℕ) → List (CMvMonomial count)
  | 0, 0 => [#v[]]
  | 0, _ + 1 => []
  | count + 1, degree =>
      (List.range (degree + 1)).flatMap fun head =>
        (weakCompositions count (degree - head)).map fun tail => tail.insertIdx 0 head

/-- The exponent vector of the homogeneous lift of an affine monomial. -/
def homogenizedMonomial {n : ℕ} (degree : ℕ) (m : CMvMonomial n) :
    CMvMonomial (n + 1) :=
  m.insertIdx 0 (degree - m.totalDegree)

/-- Projective leading monomial paired with equation `i`: `xᵢ^degree`. -/
def powerMonomial {count : ℕ} (i : Fin count) (degree : ℕ) : CMvMonomial count :=
  Vector.ofFn fun j => if j = i then degree else 0

/-- Parameter monomial for one auxiliary coefficient `uᵢ`. -/
def auxiliaryParameterMonomial {n : ℕ} (i : Fin (n + 1)) : CMvMonomial (n + 2) :=
  Vector.ofFn fun j => if j.val = i.val then 1 else 0

/-- Parameter monomial for the perturbation variable `s`. -/
def sParameterMonomial {n : ℕ} : CMvMonomial (n + 2) :=
  Vector.ofFn fun j => if j.val = n + 1 then 1 else 0

/-- Auxiliary coefficient `uᵢ`. -/
def auxiliaryCoefficient {n : ℕ} (i : Fin (n + 1)) : Parameters n F :=
  CMvPolynomial.monomial (auxiliaryParameterMonomial i) 1

/-- Perturbation coefficient `-s`. -/
def negativeS {n : ℕ} : Parameters n F :=
  CMvPolynomial.monomial sParameterMonomial (-1)

/-- A homogeneous equation as an explicit term list. -/
abbrev HomogeneousTerms (n : ℕ) (F : Type*) [Zero F] :=
  List (CMvMonomial (n + 1) × Parameters n F)

/-- Homogeneous terms of one input equation, together with `-s*xᵢ^degree`. -/
def perturbedTerms {n : ℕ} (i : Fin (n + 1)) (degree : ℕ)
    (f : CMvPolynomial n F) : HomogeneousTerms n F :=
  (f.val.toList.map fun term =>
    (homogenizedMonomial degree term.1, CMvPolynomial.C term.2)) ++
    [(powerMonomial i degree, negativeS)]

/-- Terms of `u₀x₀ + ... + uₙxₙ`. -/
def auxiliaryTerms {n : ℕ} : HomogeneousTerms n F :=
  List.ofFn fun i : Fin (n + 1) =>
    (powerMonomial i 1, auxiliaryCoefficient i)

/-- Degrees of the homogeneous equations.  Equation zero is the auxiliary
form; equation `i+1` is input equation `i`. -/
def equationDegree {n : ℕ} (system : Fin n → CMvPolynomial n F) : Fin (n + 1) → ℕ :=
  Fin.cases 1 fun i => denseDegree (system i)

/-- Homogeneous term lists in the order paired with projective variables. -/
def homogeneousTerms {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    Fin (n + 1) → HomogeneousTerms n F :=
  Fin.cases auxiliaryTerms fun i =>
    perturbedTerms (Fin.succ i) (denseDegree (system i)) (system i)

/-- Macaulay's critical homogeneous degree. -/
def macaulayDegree {n : ℕ} (system : Fin n → CMvPolynomial n F) : ℕ :=
  1 + ∑ i : Fin (n + 1), (equationDegree system i - 1)

/-- Square matrix basis of all monomials at Macaulay degree. -/
def basis {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    List (CMvMonomial (n + 1)) :=
  weakCompositions (n + 1) (macaulayDegree system)

/-- First equation whose paired leading monomial divides a basis monomial. -/
def rowEquation? {count : ℕ} (degrees : Fin count → ℕ)
    (m : CMvMonomial count) : Option (Fin count) :=
  (List.ofFn fun i : Fin count => i).find? fun i => degrees i ≤ m.get i

/-- Divide a row monomial by its assigned leading power. -/
def rowMultiplier {count : ℕ} (degree : ℕ) (i : Fin count)
    (m : CMvMonomial count) : CMvMonomial count :=
  Vector.ofFn fun j => m.get j - if j = i then degree else 0

/-- Coefficient at one matrix column in a monomial multiple of an equation. -/
def rowEntry {n : ℕ} (multiplier column : CMvMonomial (n + 1))
    (terms : HomogeneousTerms n F) : Parameters n F :=
  terms.foldl
    (fun result term => if multiplier + term.1 = column then result + term.2 else result)
    0

/-- Stored Macaulay matrix assembled solely from input coefficients.  The
fallback row is unreachable at the critical degree and remains explicit. -/
def matrix {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    Matrix (Fin (basis system).length) (Fin (basis system).length) (Parameters n F) :=
  .of fun i j =>
    let row := (basis system)[i]
    match rowEquation? (equationDegree system) row with
    | none => 0
    | some equation =>
        rowEntry (rowMultiplier (equationDegree system equation) equation row)
          (basis system)[j] (homogeneousTerms system equation)

/-- Array form used by runtime inspection of the stored matrix. -/
def matrixEntries {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    Array (Array (Parameters n F)) :=
  Array.ofFn fun i => Array.ofFn fun j => matrix system i j

/-- The runtime array has one row for every basis monomial. -/
@[simp]
theorem matrixEntries_size {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    (matrixEntries system).size = (basis system).length := by
  simp [matrixEntries]

/-- Every runtime row has one entry for every basis monomial. -/
@[simp]
theorem matrixEntries_row_size {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (i : Fin (basis system).length) :
    ((matrixEntries system)[i]).size = (basis system).length := by
  simp [matrixEntries]

/-- Macaulay determinant candidate for the generalized characteristic.  The
resultant quotient theorem is a later proof obligation. -/
def characteristic {n : ℕ} (system : Fin n → CMvPolynomial n F) : Parameters n F :=
  (matrix system).det

/-- The executed characteristic is definitionally the determinant of the
stored input-derived matrix. -/
theorem characteristic_eq_det {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    characteristic system = (matrix system).det := rfl

/-- Exponent of `s` in a parameter monomial. -/
def sExponent {n : ℕ} (m : CMvMonomial (n + 2)) : ℕ := m.get ⟨n + 1, by omega⟩

/-- Drop the final `s` exponent, retaining `(u₀,...,uₙ)`. -/
def dropS {n : ℕ} (m : CMvMonomial (n + 2)) : CMvMonomial (n + 1) :=
  Vector.ofFn fun i => m.get ⟨i.val, by omega⟩

/-- Coefficient of one power of `s` in a parameter polynomial. -/
def coefficientInS {n : ℕ} (degree : ℕ) (H : Parameters n F) :
    CMvPolynomial (n + 1) F :=
  H.val.toList.foldl
    (fun result term =>
      if sExponent term.1 = degree then
        CMvPolynomial.monomial (dropS term.1) term.2 + result
      else result)
    0

/-- Lowest stored exponent of `s`.  Canonical sparse storage makes this
equivalent to scanning coefficients from zero upward. -/
def lowestSExponent? {n : ℕ} (H : Parameters n F) : Option ℕ :=
  (H.monomials.map sExponent).min?

/-- Lowest nonzero `s`-coefficient of the executed Macaulay determinant. -/
def perturbation? {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    Option (CMvPolynomial (n + 1) F) :=
  match lowestSExponent? (characteristic system) with
  | none => none
  | some degree => some (coefficientInS degree (characteristic system))

/-- Complete stored result of a successful matrix construction. -/
structure Output (n : ℕ) where
  supports : Fin n → List (CMvMonomial n)
  degrees : Fin n → ℕ
  macaulayDegree : ℕ
  matrixSize : ℕ
  characteristic : Parameters n F
  perturbationDegree : ℕ
  perturbation : CMvPolynomial (n + 1) F

/-- A zero characteristic is represented explicitly.  Zero and constant input
equations are otherwise valid inputs. -/
inductive ProducerError where
  | zeroCharacteristic
  deriving BEq

/-- Compute sparse metadata, the dense perturbing terms, the Macaulay
determinant, and its lowest nonzero `s`-coefficient. -/
def run {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    Except ProducerError (Output n (F := F)) :=
  let H := characteristic system
  match lowestSExponent? H with
  | none => .error .zeroCharacteristic
  | some degree => .ok
      { supports := fun i => sparseSupport (system i)
        degrees := fun i => denseDegree (system i)
        macaulayDegree := macaulayDegree system
        matrixSize := (basis system).length
        characteristic := H
        perturbationDegree := degree
        perturbation := coefficientInS degree H }

omit [BEq F] [LawfulBEq F] in
@[simp]
theorem denseDegree_pos {n : ℕ} (f : CMvPolynomial n F) : 0 < denseDegree f := by
  simp [denseDegree]

/-- Successful execution freezes the determinant, selected exponent, and
coefficient actually computed by `run`. -/
theorem run_ok_computed {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (output : Output n (F := F)) (houtput : run system = .ok output) :
    output.characteristic = characteristic system ∧
      lowestSExponent? (characteristic system) = some output.perturbationDegree ∧
      output.perturbation = coefficientInS output.perturbationDegree
        (characteristic system) := by
  unfold run at houtput
  cases hdegree : lowestSExponent? (characteristic system) with
  | none => simp [hdegree] at houtput
  | some degree =>
      simp only [hdegree, Except.ok.injEq] at houtput
      subst output
      simp

end ArkLib.Rojas.Producer.DenseMacaulay
