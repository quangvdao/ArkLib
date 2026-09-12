/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerRepresentation
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Constructive inversion in a bounded-fiber tower

This file implements the finite-dimensional linear-algebra step behind inverse materialization in
`(F[U]/G)[V]/h`.  Multiplication matrices and coordinate vectors are deliberately implementation
details: the exported operation consumes and returns ordinary reduced tower representatives.

The algorithm uses the canonical monomial slice `U^i V^j`, forms multiplication by the input on
that slice, and solves the system for `1` by Cramer's rule.  The decoded candidate is reduced back
through `TowerRepresentation.reduceElement` and is accepted only after direct left- and right-hand
multiplication checks in the same quotient representation.  Thus a representation bug in the
linear solve can never manufacture a false inverse.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly Matrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

private abbrev CoordinateIndex (G : CPolynomial F)
    (h : CPolynomial (CPolynomial F)) :=
  Fin h.natDegree × Fin G.natDegree

/-- Read the coefficient of `U^i V^j` from a nested polynomial. -/
private def coordinate (G : CPolynomial F) (h p : CPolynomial (CPolynomial F))
    (ij : CoordinateIndex G h) : F :=
  (p.coeff ij.1.val).coeff ij.2.val

/-- Re-encode a coordinate vector as a nested computable polynomial. -/
private def ofCoordinates (G : CPolynomial F) (h : CPolynomial (CPolynomial F))
    (x : CoordinateIndex G h → F) : CPolynomial (CPolynomial F) :=
  CPolynomial.ofArray <| Array.ofFn fun j : Fin h.natDegree ↦
    CPolynomial.ofArray <| Array.ofFn fun i : Fin G.natDegree ↦ x (j, i)

/-- The canonical monomial `U^i V^j` corresponding to one quotient coordinate. -/
private def basisElement (G : CPolynomial F) (h : CPolynomial (CPolynomial F))
    (ij : CoordinateIndex G h) : CPolynomial (CPolynomial F) :=
  CPolynomial.monomial ij.1.val (CPolynomial.monomial ij.2.val (1 : F))

/-- Matrix of multiplication by `u`, with every product reduced in the actual tower quotient.
This is intentionally private: callers should reason about `inverseRepresentative?`, not about a
particular choice of coordinates. -/
private def multiplicationMatrix (G : CPolynomial F) (h u : CPolynomial (CPolynomial F)) :
    Matrix (CoordinateIndex G h) (CoordinateIndex G h) F :=
  fun row col ↦ coordinate G h
    (TowerRepresentation.reduceElement G h (u * basisElement G h col)) row

/-- Coordinates of the quotient unit. -/
private def oneCoordinates (G : CPolynomial F) (h : CPolynomial (CPolynomial F)) :
    CoordinateIndex G h → F :=
  coordinate G h (TowerRepresentation.reduceElement G h 1)

/-- Decode the Cramer solution and immediately project it back to the canonical quotient slice. -/
private def cramerCandidate (G : CPolynomial F) (h u : CPolynomial (CPolynomial F)) :
    CPolynomial (CPolynomial F) :=
  let M := multiplicationMatrix G h u
  let rhs := oneCoordinates G h
  let x : CoordinateIndex G h → F := fun i ↦ M.det⁻¹ * M.cramer rhs i
  TowerRepresentation.reduceElement G h (ofCoordinates G h x)

/-- Direct executable verification that `v` is a two-sided inverse of `u` modulo the tower ideal. -/
private def verifiesInverse (G : CPolynomial F) (h u v : CPolynomial (CPolynomial F)) : Bool :=
  (TowerRepresentation.reduceElement G h (u * v) ==
      TowerRepresentation.reduceElement G h 1) &&
    (TowerRepresentation.reduceElement G h (v * u) ==
      TowerRepresentation.reduceElement G h 1)

private theorem verifiesInverse_eq_true_iff
    (G : CPolynomial F) (h u v : CPolynomial (CPolynomial F)) :
    verifiesInverse G h u v = true ↔
      TowerRepresentation.reduceElement G h (u * v) =
          TowerRepresentation.reduceElement G h 1 ∧
        TowerRepresentation.reduceElement G h (v * u) =
          TowerRepresentation.reduceElement G h 1 := by
  simp [verifiesInverse]

/-- Quotient-level unitness stated independently of the inversion algorithm. -/
def IsTowerUnit (G : CPolynomial F) (h u : CPolynomial (CPolynomial F)) : Prop :=
  ∃ v : CPolynomial (CPolynomial F),
    TowerRepresentation.reduceElement G h (u * v) =
        TowerRepresentation.reduceElement G h 1 ∧
      TowerRepresentation.reduceElement G h (v * u) =
        TowerRepresentation.reduceElement G h 1

/-- Compute a two-sided inverse representative in `(F[U]/G)[V]/h`.

`none` is an explicit failure signal.  A zero multiplication determinant is rejected immediately;
a nonzero determinant is solved by Cramer's rule, re-encoded, reduced, and finally checked by
actual multiplication in the tower quotient before it is returned. -/
def inverseRepresentative? (G : CPolynomial F) (h u : CPolynomial (CPolynomial F)) :
    Option (CPolynomial (CPolynomial F)) :=
  let M := multiplicationMatrix G h u
  if M.det == 0 then
    none
  else
    let candidate := cramerCandidate G h u
    if verifiesInverse G h u candidate then some candidate else none

/-- Every successful result is a left inverse modulo the full tower ideal. -/
theorem inverseRepresentative?_mul_eq_one
    (G : CPolynomial F) (h u v : CPolynomial (CPolynomial F))
    (hv : inverseRepresentative? G h u = some v) :
    TowerRepresentation.reduceElement G h (u * v) =
      TowerRepresentation.reduceElement G h 1 := by
  unfold inverseRepresentative? at hv
  split at hv
  · simp at hv
  · split at hv
    · have hverify :=
        (verifiesInverse_eq_true_iff G h u (cramerCandidate G h u)).mp ‹_›
      simp at hv
      subst v
      exact hverify.1
    · simp at hv

/-- Every successful result is a right inverse modulo the full tower ideal. -/
theorem inverseRepresentative?_mul_eq_one_right
    (G : CPolynomial F) (h u v : CPolynomial (CPolynomial F))
    (hv : inverseRepresentative? G h u = some v) :
    TowerRepresentation.reduceElement G h (v * u) =
      TowerRepresentation.reduceElement G h 1 := by
  unfold inverseRepresentative? at hv
  split at hv
  · simp at hv
  · split at hv
    · have hverify :=
        (verifiesInverse_eq_true_iff G h u (cramerCandidate G h u)).mp ‹_›
      simp at hv
      subst v
      exact hverify.2
    · simp at hv

/-- Successful computation proves unitness in the independently stated quotient sense. -/
theorem isTowerUnit_of_inverseRepresentative?_eq_some
    (G : CPolynomial F) (h u v : CPolynomial (CPolynomial F))
    (hv : inverseRepresentative? G h u = some v) : IsTowerUnit G h u := by
  exact ⟨v, inverseRepresentative?_mul_eq_one G h u v hv,
    inverseRepresentative?_mul_eq_one_right G h u v hv⟩

/-- Successful inversion always returns a representative in the canonical bounded tower slice. -/
theorem inverseRepresentative?_elementReduced
    {G : CPolynomial F} (hG : G.monic)
    {h u v : CPolynomial (CPolynomial F)} (hh : h.monic) (hhpos : 0 < h.natDegree)
    (hv : inverseRepresentative? G h u = some v) :
    TowerRepresentation.ElementReduced G h v := by
  unfold inverseRepresentative? at hv
  split at hv
  · simp at hv
  · split at hv
    · simp at hv
      subst v
      exact TowerRepresentation.elementReduced_reduceElement hG hh hhpos _
    · simp at hv

end ReedSolomon.ListDecoding.TowerAlgebra
