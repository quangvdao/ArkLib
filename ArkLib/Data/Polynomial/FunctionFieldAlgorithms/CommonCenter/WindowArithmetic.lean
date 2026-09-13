/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.WindowSemantics

/-!
# Executable arithmetic clients of the normalization windows

A finite congruence test compares the actual reduced numerator arrays. Polynomial-table
multiplication constructs representatives for the product tests in the third window.
The multiplication table is finite input, not an assumption of normality. In particular,
products are formed from chosen representatives; this does not incorrectly assert that
multiplication descends from `d⁻¹O/dO × d⁻¹O/dO` to `d⁻²O/dO`.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter

open CompPoly

variable {K : Type*} [Field K] [BEq K] [LawfulBEq K]

local instance : DecidableEq K := instDecidableEqOfLawfulBEq

/-- Exact executable equality test in a numerator window. -/
def sameWindow {rank : ℕ} (layers : ℕ) (d : CPolynomial K)
    (p q : Fin rank → CPolynomial K) : Bool :=
  decide (reduceWindow layers d p = reduceWindow layers d q)

/-- The finite test decides actual fractional lattice congruence, under a monic modulus. -/
theorem sameWindow_eq_true_iff {rank : ℕ} (denominator lattice : ℕ)
    (d : CPolynomial K) (hd : d.toPoly.Monic) (p q : Fin rank → CPolynomial K) :
    sameWindow (denominator + lattice) d p q = true ↔
      PolynomialLatticeCongruent d.toPoly lattice
        (fractionalCoordinates d.toPoly denominator (fun i => (p i).toPoly))
        (fractionalCoordinates d.toPoly denominator (fun i => (q i).toPoly)) := by
  simpa only [sameWindow, decide_eq_true_eq] using
    reduce_window_eq_iff_fractional_congruence denominator lattice d hd p q

/-- Multiplication constants in a supplied free polynomial basis. -/
abbrev PolynomialMultiplicationTable (K : Type*) [Zero K] [BEq K] (rank : ℕ) :=
  Fin rank → Fin rank → Fin rank → CPolynomial K

/-- Multiply finite polynomial numerator tuples using the supplied table. -/
def multiplyNumerators {rank : ℕ} (table : PolynomialMultiplicationTable K rank)
    (p q : Fin rank → CPolynomial K) : Fin rank → CPolynomial K :=
  fun k => ∑ i, ∑ j, table i j k * p i * q j

/-- The same supplied table acts on rational-function coordinate tuples. -/
noncomputable def fractionalTableProduct {rank : ℕ}
    (table : PolynomialMultiplicationTable K rank) (x y : Fin rank → RatFunc K) :
    Fin rank → RatFunc K :=
  fun k => ∑ i, ∑ j, algebraMap (Polynomial K) (RatFunc K) (table i j k).toPoly * x i * y j

/-- Executable numerator multiplication corresponds to actual table multiplication of the
fractional coordinate vectors, with denominator exponents adding exactly. -/
theorem fractionalCoordinates_multiplyNumerators {rank : ℕ}
    (table : PolynomialMultiplicationTable K rank) (d : CPolynomial K)
    (a b : ℕ) (p q : Fin rank → CPolynomial K) :
    fractionalCoordinates d.toPoly (a + b)
        (fun k => (multiplyNumerators table p q k).toPoly) =
      fractionalTableProduct table
        (fractionalCoordinates d.toPoly a (fun i => (p i).toPoly))
        (fractionalCoordinates d.toPoly b (fun i => (q i).toPoly)) := by
  funext k
  simp only [fractionalCoordinates, multiplyNumerators, fractionalTableProduct,
    CPolynomial.toPoly_sum, CPolynomial.toPoly_mul, map_sum, map_mul,
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [pow_add, mul_inv_rev]
  ring

/-- Form products of the chosen second-window representatives in the third window. -/
def multiplyRepresentatives {rank : ℕ} (table : PolynomialMultiplicationTable K rank)
    (d : CPolynomial K) (x y : Window K rank d.natDegree 2) :
    Window K rank d.natDegree 3 :=
  thirdWindow d (multiplyNumerators table (decodeWindow x) (decodeWindow y))

/-- The returned third-window tuple compares equal exactly when the actual table product
of the chosen rational representatives belongs to the specified fractional lattice class. -/
theorem multiplyRepresentatives_eq_iff {rank : ℕ}
    (table : PolynomialMultiplicationTable K rank) (d : CPolynomial K) (hd : d.toPoly.Monic)
    (x y : Window K rank d.natDegree 2) (q : Fin rank → CPolynomial K) :
    multiplyRepresentatives table d x y = thirdWindow d q ↔
      PolynomialLatticeCongruent d.toPoly 1
        (fractionalTableProduct table
          (fractionalCoordinates d.toPoly 1 (fun i => (decodeWindow x i).toPoly))
          (fractionalCoordinates d.toPoly 1 (fun i => (decodeWindow y i).toPoly)))
        (fractionalCoordinates d.toPoly 2 (fun i => (q i).toPoly)) := by
  rw [← fractionalCoordinates_multiplyNumerators table d 1 1]
  exact third_window_eq_iff d hd _ q

end Polynomial.FunctionFieldAlgorithms.CommonCenter
