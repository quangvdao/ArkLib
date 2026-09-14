/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.WindowArithmetic
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Fractional-window acceptance and runtime clients

These tests distinguish the three quotient lattices, exercise nontrivial monic remainder
arithmetic, and exhibit the cusp-table candidate `v/u` with square `u`. The cusp checks
are finite table/lattice checks, not a claim that the normalization algorithm is complete.
-/

namespace CommonCenterWindowTests

open CompPoly Polynomial.FunctionFieldAlgorithms.CommonCenter

private def u : CPolynomial ℚ := CPolynomial.X
private def quadratic : CPolynomial ℚ := u ^ 2 + u + 1
private def cuspDiscriminant : CPolynomial ℚ := u ^ 3

/-- Polynomial ring fixture for the already-normal rank-one case. -/
example : IsIntegrallyClosed (Polynomial ℚ) := inferInstance

/-- Multiplication in the free basis `(1,v)` with relation `v²=u³`. -/
private def cuspTable : PolynomialMultiplicationTable ℚ 2 := fun i j k =>
  if i = 0 ∧ j = 0 ∧ k = 0 then 1
  else if (i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0) ∧ k = 1 then 1
  else if i = 1 ∧ j = 1 ∧ k = 0 then u ^ 3 else 0

/-- Numerator of `v/u` when the common denominator is `d=u³`. -/
private def cuspCandidate : Fin 2 → CPolynomial ℚ := ![0, u ^ 2]

/-- The exact square numerator is `(u⁷,0)`, representing `u` with denominator `d²`. -/
private def cuspSquare : Fin 2 → CPolynomial ℚ := ![u ^ 7, 0]

/-- Distinct import client: a finite checker result yields the rational-lattice fact. -/
example {rank : ℕ} (d : CPolynomial ℚ) (hd : d.toPoly.Monic)
    (p : Fin rank → CPolynomial ℚ) (h : sameWindow 1 d p 0 = true) :
    PolynomialLatticeCongruent d.toPoly 0
      (fractionalCoordinates d.toPoly 1 (fun i => (p i).toPoly))
      (fractionalCoordinates d.toPoly 1 (fun _ => (0 : CPolynomial ℚ).toPoly)) :=
  (sameWindow_eq_true_iff 1 0 d hd p 0).mp h

/-- The cusp-table fraction is provably outside the original polynomial coordinate lattice.
This is a semantic consequence of the executable checker, not only a runtime assertion. -/
example : ¬ PolynomialLatticeCongruent cuspDiscriminant.toPoly 0
    (fractionalCoordinates cuspDiscriminant.toPoly 1 (fun i => (cuspCandidate i).toPoly))
    (fractionalCoordinates cuspDiscriminant.toPoly 1
      (fun _ : Fin 2 => (0 : CPolynomial ℚ).toPoly)) := by
  have hd : cuspDiscriminant.toPoly.Monic := by
    simp [cuspDiscriminant, u, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
  intro h
  have hcheck := (sameWindow_eq_true_iff 1 0 cuspDiscriminant hd cuspCandidate
    (fun _ => 0)).mpr h
  have hreject : sameWindow 1 cuspDiscriminant cuspCandidate (fun _ => 0) = false := by
    decide +kernel
  rw [hreject] at hcheck
  contradiction

/-- Its squared numerator represents an element of the original lattice. Together with the
actual table-product calculation below, this detects the nonnormal-style cusp obstruction. -/
example : PolynomialLatticeCongruent cuspDiscriminant.toPoly 0
    (fractionalCoordinates cuspDiscriminant.toPoly 2 (fun i => (cuspSquare i).toPoly))
    (fractionalCoordinates cuspDiscriminant.toPoly 2
      (fun _ : Fin 2 => (0 : CPolynomial ℚ).toPoly)) := by
  have hd : cuspDiscriminant.toPoly.Monic := by
    simp [cuspDiscriminant, u, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
  apply (sameWindow_eq_true_iff 2 0 cuspDiscriminant hd cuspSquare 0).mp
  decide +kernel

/-- Branch-sensitive finite calculations; no enumeration of field elements is used. -/
def runTests : IO Unit := do
  let oneCoordinate (p : CPolynomial ℚ) : Fin 1 → CPolynomial ℚ := fun _ => p
  unless sameWindow 1 quadratic (oneCoordinate (quadratic + u)) (oneCoordinate u) do
    throw (IO.userError "monic reduction was replaced by coefficient truncation")
  unless !sameWindow 1 quadratic (oneCoordinate (u + 1)) (oneCoordinate u) do
    throw (IO.userError "different quotient classes were identified")
  unless sameWindow 1 u (oneCoordinate u) 0 &&
      !sameWindow 2 u (oneCoordinate u) 0 &&
      sameWindow 2 u (oneCoordinate (u ^ 2)) 0 &&
      !sameWindow 3 u (oneCoordinate (u ^ 2)) 0 &&
      sameWindow 3 u (oneCoordinate (u ^ 3)) 0 do
    throw (IO.userError "the three lattice moduli were confused")
  -- Equal second-window classes can have different third-window products before fixing lifts.
  let scalarTable : PolynomialMultiplicationTable ℚ 1 := fun _ _ _ => 1
  unless sameWindow 2 u (oneCoordinate (u ^ 2)) 0 &&
      !sameWindow 3 u
        (multiplyNumerators scalarTable (oneCoordinate 1) (oneCoordinate (u ^ 2))) 0 do
    throw (IO.userError "representative multiplication incorrectly descended to quotient classes")
  unless sameWindow 3 (1 : CPolynomial ℚ) (oneCoordinate (u ^ 7)) 0 &&
      sameWindow 0 quadratic (oneCoordinate (u ^ 7)) 0 do
    throw (IO.userError "unit/zero-width windows did not collapse")
  unless !sameWindow 1 cuspDiscriminant cuspCandidate 0 do
    throw (IO.userError "cusp candidate v/u was incorrectly integral in the original lattice")
  unless multiplyNumerators cuspTable cuspCandidate cuspCandidate == cuspSquare do
    throw (IO.userError "cusp candidate failed the exact square relation")
  unless sameWindow 2 cuspDiscriminant cuspSquare 0 do
    throw (IO.userError "cusp candidate square did not lie in the original lattice")
  let x := secondWindow cuspDiscriminant cuspCandidate
  unless decide (multiplyRepresentatives cuspTable cuspDiscriminant x x =
      thirdWindow cuspDiscriminant cuspSquare) do
    throw (IO.userError "chosen representative multiplication disagreed with the table")
  IO.println "fractional-window congruence, representative products, and cusp fixtures: passed"

#print axioms decode_reduce_window
#print axioms reduce_decode_window
#print axioms reduce_window_eq_iff
#print axioms fractional_lattice_congruent_iff
#print axioms reduce_window_eq_iff_fractional_congruence
#print axioms sameWindow_eq_true_iff
#print axioms fractionalCoordinates_multiplyNumerators
#print axioms multiplyRepresentatives_eq_iff

end CommonCenterWindowTests

/-- Run the finite-window client as a standalone executable. -/
def commonCenterWindowSemanticsStandaloneMain : IO Unit := CommonCenterWindowTests.runTests
