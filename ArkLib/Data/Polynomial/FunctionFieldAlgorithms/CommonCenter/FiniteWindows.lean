/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.FiniteEquations
public import CompPoly.Univariate.Basic

/-!
# Stored numerator windows

The three spaces in bounded normalization use coefficient arrays for numerators modulo
`d`, `d²`, and `d³`. These routines perform the corresponding polynomial reductions. The
free order basis and its multiplication table are supplied separately. No integral closure
is selected, and these routines do not assert that an arbitrary table represents an order.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter

open CompPoly

variable {K : Type*} [Field K] [BEq K] [LawfulBEq K]

/-- Read a polynomial tuple into fixed-width numerator coefficient storage. -/
def encodeWindow {rank degree layers : ℕ} (p : Fin rank → CPolynomial K) :
    Window K rank degree layers := fun i j => (p i).coeff j

/-- Materialize numerator polynomials from their fixed-width coefficient storage. -/
def decodeWindow {rank degree layers : ℕ} (x : Window K rank degree layers) :
    Fin rank → CPolynomial K := fun i => CPolynomial.ofArray (Array.ofFn (x i))

/-- Coordinatewise numerator remainder. For a monic `d` of degree `degree`, the output
coefficients give canonical representatives modulo `d ^ layers`. -/
def reduceWindow {rank : ℕ} (layers : ℕ) (d : CPolynomial K)
    (p : Fin rank → CPolynomial K) : Window K rank d.natDegree layers :=
  encodeWindow (fun i => CPolynomial.modByMonic (p i) (d ^ layers))

/-- The first space: numerators of `d⁻¹O/O` are reduced modulo `d`. -/
def firstWindow {rank : ℕ} (d : CPolynomial K) (p : Fin rank → CPolynomial K) :
    Window K rank d.natDegree 1 := reduceWindow 1 d p

/-- The second space: numerators of `d⁻¹O/dO` are reduced modulo `d²`. -/
def secondWindow {rank : ℕ} (d : CPolynomial K) (p : Fin rank → CPolynomial K) :
    Window K rank d.natDegree 2 := reduceWindow 2 d p

/-- The third space: numerators of `d⁻²O/dO` are reduced modulo `d³`. -/
def thirdWindow {rank : ℕ} (d : CPolynomial K) (p : Fin rank → CPolynomial K) :
    Window K rank d.natDegree 3 := reduceWindow 3 d p

/-- Re-materializing the finite numerator representation preserves every stored cell. -/
theorem encode_decode_window {rank degree layers : ℕ}
    (x : Window K rank degree layers) : encodeWindow (decodeWindow x) = x := by
  funext i j
  simp [encodeWindow, decodeWindow, CPolynomial.coeff_ofArray, Array.getD]

end Polynomial.FunctionFieldAlgorithms.CommonCenter
