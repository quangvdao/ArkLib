/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CenterShiftMachine

/-! # Changing centered ascending coefficients to descending message coefficients -/

@[expose] public section

namespace Polynomial.CoefficientList

open JetHornerMachine

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Translate the ascending coefficients at `center` into descending coefficients at zero.
The physical width, including leading zeros, is preserved. -/
def centeredToDescending (center : R) (cs : List R) : List R :=
  (jetLoop (-center) cs.reverse (List.replicate cs.length 0)).reverse

@[simp] theorem centeredToDescending_length (center : R) (cs : List R) :
    (centeredToDescending center cs).length = cs.length := by
  simp [centeredToDescending]

private theorem map_jetUpdate (f : R →+* S) (x carry : R) (cs : List R) :
    (jetUpdate x carry cs).map f = jetUpdate (f x) (f carry) (cs.map f) := by
  induction cs generalizing carry with
  | nil => rfl
  | cons c cs ih => simp [jetUpdate, ih]

private theorem map_jetLoop (f : R →+* S) (x : R) (cs js : List R) :
    (jetLoop x cs js).map f = jetLoop (f x) (cs.map f) (js.map f) := by
  induction cs generalizing js with
  | nil => rfl
  | cons c cs ih => simp [jetLoop, ih, map_jetUpdate]

/-- The executed arithmetic change of basis commutes with every ring homomorphism. -/
theorem map_centeredToDescending (f : R →+* S) (center : R) (cs : List R) :
    (centeredToDescending center cs).map f =
      centeredToDescending (f center) (cs.map f) := by
  simp [centeredToDescending, List.map_reverse, map_jetLoop]

/-- Semantics of the complete width-preserving change of basis, including width zero. -/
theorem centeredToDescending_polynomial (center : R) (cs : List R) :
    coefficientPolynomial (centeredToDescending center cs) =
      taylor (-center) (ascendingPolynomial cs) := by
  cases hlen : cs.length with
  | zero =>
      have : cs = [] := List.length_eq_zero_iff.mp hlen
      subst cs
      simp [centeredToDescending, jetLoop, coefficientPolynomial, ascendingPolynomial]
  | succ d =>
      let input : ReedSolomon.HiddenDerivative.CenterShiftMachine.Input R :=
        ⟨cs.reverse, center, d⟩
      simpa [ReedSolomon.HiddenDerivative.CenterShiftMachine.outputSpec_eq_reverse,
        ReedSolomon.HiddenDerivative.CenterShiftMachine.jetSpec, input,
        centeredToDescending, ascendingPolynomial, hlen] using
        ReedSolomon.HiddenDerivative.CenterShiftMachine.outputSpec_polynomial input
          (by simp [input, hlen])

/-- Actual centered Taylor coefficients reconstruct the original message, with no assumption
that its center is zero. -/
theorem centeredToDescending_taylor (center : R) (p : R[X]) (k : ℕ)
    (hdegree : p.degree < k) :
    coefficientPolynomial (centeredToDescending center
      (List.ofFn fun j : Fin k => (taylor center p).coeff j)) = p := by
  rw [centeredToDescending_polynomial,
    ascendingPolynomial_ofFn k (taylor center p) (by simpa using hdegree),
    taylor_taylor, neg_add_cancel, taylor_zero]

end Polynomial.CoefficientList
