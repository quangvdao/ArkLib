/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.FiniteWindows
public import CompPoly.Univariate.DivisionCorrectness
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Exact semantics of the three normalization windows

The executed coefficient windows represent numerator congruences modulo powers of a monic
polynomial. These are exactly congruences in the fractional polynomial lattices occurring in
`lem:decoder-bounded-normalization`: `d⁻¹O/O`, `d⁻¹O/dO`, and `d⁻²O/dO`, after choosing a
free polynomial basis of `O`. The ambient coordinates are explicit rational functions;
there is no chosen integral closure or normality assumption.

This file proves representation semantics. Constructing a bounded separable monic projection
and its nonzero discriminant, the reverse trace-radical theorem, and the Grauert–Remmert
stabilization criterion remain separate normalization obligations. In particular, the unclosed
projection existence theorem must find a shear `u=Y+λZ`, with `λ` in the integer prefix
`0,...,2B`, making the transformed equation monic and separable under the paper's reducedness,
coprimality, degree, and characteristic hypotheses. No such theorem is assumed here.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter

open CompPoly

variable {K : Type*} [Field K] [BEq K] [LawfulBEq K]

/-- No numerator information is lost by the finite coefficient encoding when its tail is zero. -/
theorem decode_encode_window {rank degree layers : ℕ}
    (p : Fin rank → CPolynomial K)
    (hbound : ∀ i j, layers * degree ≤ j → (p i).coeff j = 0) :
    decodeWindow (encodeWindow (degree := degree) (layers := layers) p) = p := by
  funext i
  apply CPolynomial.eq_iff_coeff.mpr
  intro j
  by_cases hj : j < layers * degree
  · simp [decodeWindow, encodeWindow, CPolynomial.coeff_ofArray, Array.getD, hj]
  · simp [decodeWindow, CPolynomial.coeff_ofArray, Array.getD, hj,
      hbound i j (by omega)]

/-- Remainders modulo the `layers`-th power have no coefficients outside that window,
including a constant monic divisor and a zero-layer window. -/
theorem remainder_coeff_eq_zero (layers : ℕ) (d p : CPolynomial K)
    (hd : d.toPoly.Monic) (j : ℕ) (hj : layers * d.natDegree ≤ j) :
    (CPolynomial.modByMonic p (d ^ layers)).coeff j = 0 := by
  have hpow : (d ^ layers).monic :=
    (CPolynomial.monic_toPoly_iff _).mpr (by simpa [CPolynomial.toPoly_pow] using hd.pow layers)
  rw [CPolynomial.coeff_toPoly, CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hpow,
    CPolynomial.toPoly_pow]
  apply Polynomial.coeff_eq_zero_of_degree_lt
  apply (Polynomial.degree_modByMonic_lt _ (hd.pow layers)).trans_le
  rw [Polynomial.degree_eq_natDegree (hd.pow layers).ne_zero, Polynomial.natDegree_pow]
  simpa only [CPolynomial.natDegree_toPoly, Nat.mul_comm] using
    (show (↑(layers * d.natDegree) : WithBot ℕ) ≤ ↑j by exact_mod_cast hj)

/-- Decoding the actual reduction returns its full polynomial remainder, not a truncation. -/
theorem decode_reduce_window {rank : ℕ} (layers : ℕ) (d : CPolynomial K)
    (hd : d.toPoly.Monic) (p : Fin rank → CPolynomial K) :
    decodeWindow (reduceWindow layers d p) =
      fun i => CPolynomial.modByMonic (p i) (d ^ layers) := by
  apply decode_encode_window
  intro i j hj
  exact remainder_coeff_eq_zero layers d (p i) hd j hj

/-- Every finite window is already a reduced numerator after decoding. -/
theorem reduce_decode_window {rank : ℕ} (layers : ℕ) (d : CPolynomial K)
    (hd : d.toPoly.Monic) (x : Window K rank d.natDegree layers) :
    reduceWindow layers d (decodeWindow x) = x := by
  have hpow : (d ^ layers).monic :=
    (CPolynomial.monic_toPoly_iff _).mpr (by simpa [CPolynomial.toPoly_pow] using hd.pow layers)
  have hrem : (fun i => CPolynomial.modByMonic (decodeWindow x i) (d ^ layers)) =
      decodeWindow x := by
    funext i
    apply CPolynomial.ringEquiv.injective
    simp only [CPolynomial.ringEquiv_apply]
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hpow, CPolynomial.toPoly_pow]
    apply (Polynomial.modByMonic_eq_self_iff (hd.pow layers)).mpr
    rw [Polynomial.degree_eq_natDegree (hd.pow layers).ne_zero, Polynomial.natDegree_pow,
      ← CPolynomial.natDegree_toPoly]
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro j hj
    rw [← CPolynomial.coeff_toPoly]
    simp [decodeWindow, CPolynomial.coeff_ofArray, Array.getD, Nat.not_lt.mpr hj]
  simpa only [reduceWindow, hrem] using encode_decode_window x

/-- Equality of the executed finite windows is precisely numerator divisibility. -/
theorem reduce_window_eq_iff {rank : ℕ} (layers : ℕ) (d : CPolynomial K)
    (hd : d.toPoly.Monic) (p q : Fin rank → CPolynomial K) :
    reduceWindow layers d p = reduceWindow layers d q ↔
      ∀ i, d.toPoly ^ layers ∣ (p i).toPoly - (q i).toPoly := by
  have hpow : (d ^ layers).monic :=
    (CPolynomial.monic_toPoly_iff _).mpr (by simpa [CPolynomial.toPoly_pow] using hd.pow layers)
  have hremainder (i : Fin rank) :
      CPolynomial.modByMonic (p i) (d ^ layers) =
        CPolynomial.modByMonic (q i) (d ^ layers) ↔
      d.toPoly ^ layers ∣ (p i).toPoly - (q i).toPoly := by
    rw [← CPolynomial.ringEquiv.injective.eq_iff]
    simp only [CPolynomial.ringEquiv_apply]
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hpow,
      CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hpow, CPolynomial.toPoly_pow,
      ← sub_eq_zero, ← Polynomial.sub_modByMonic,
      Polynomial.modByMonic_eq_zero_iff_dvd (hd.pow layers)]
  constructor
  · intro h i
    have h' := congrArg (fun x => decodeWindow x i) h
    rw [decode_reduce_window layers d hd p, decode_reduce_window layers d hd q] at h'
    exact (hremainder i).mp h'
  · intro h
    unfold reduceWindow
    congr 1
    funext i
    exact (hremainder i).mpr (h i)

/-- Explicit fractional coordinates in a chosen free polynomial basis. The mathematical
rational-function target is used only for semantics; runtime representatives remain stored
polynomial numerator windows. -/
noncomputable def fractionalCoordinates {rank : ℕ} (d : Polynomial K) (denominator : ℕ)
    (p : Fin rank → Polynomial K) : Fin rank → RatFunc K :=
  fun i => algebraMap (Polynomial K) (RatFunc K) (p i) /
    algebraMap (Polynomial K) (RatFunc K) d ^ denominator

/-- Congruence modulo `d ^ lattice` times the free polynomial lattice. -/
def PolynomialLatticeCongruent {rank : ℕ} (d : Polynomial K) (lattice : ℕ)
    (x y : Fin rank → RatFunc K) : Prop :=
  ∃ r : Fin rank → Polynomial K, ∀ i,
    x i - y i = algebraMap (Polynomial K) (RatFunc K) d ^ lattice *
      algebraMap (Polynomial K) (RatFunc K) (r i)

omit [BEq K] [LawfulBEq K] in
/-- Clearing the explicit fractional denominator gives the exact polynomial equation. -/
theorem fractional_difference_eq_iff (d p q r : Polynomial K) (hd : d ≠ 0)
    (denominator lattice : ℕ) :
    algebraMap (Polynomial K) (RatFunc K) p /
        algebraMap (Polynomial K) (RatFunc K) d ^ denominator -
      algebraMap (Polynomial K) (RatFunc K) q /
        algebraMap (Polynomial K) (RatFunc K) d ^ denominator =
      algebraMap (Polynomial K) (RatFunc K) d ^ lattice *
        algebraMap (Polynomial K) (RatFunc K) r ↔
      p - q = d ^ (denominator + lattice) * r := by
  have hd' : algebraMap (Polynomial K) (RatFunc K) d ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hd
  have heq :
      (algebraMap (Polynomial K) (RatFunc K) d ^ lattice *
        algebraMap (Polynomial K) (RatFunc K) r) *
        algebraMap (Polynomial K) (RatFunc K) d ^ denominator =
      algebraMap (Polynomial K) (RatFunc K) (d ^ (denominator + lattice) * r) := by
    simp only [map_mul, map_pow, pow_add]
    ring
  rw [← sub_div, div_eq_iff (pow_ne_zero _ hd'), heq, ← map_sub,
    (RatFunc.algebraMap_injective K).eq_iff]

omit [BEq K] [LawfulBEq K] in
/-- Fractional lattice congruence is exactly divisibility by the sum of the two powers. -/
theorem fractional_lattice_congruent_iff {rank : ℕ} (d : Polynomial K) (hd : d ≠ 0)
    (denominator lattice : ℕ) (p q : Fin rank → Polynomial K) :
    PolynomialLatticeCongruent d lattice
      (fractionalCoordinates d denominator p) (fractionalCoordinates d denominator q) ↔
      ∀ i, d ^ (denominator + lattice) ∣ p i - q i := by
  classical
  simp only [PolynomialLatticeCongruent, fractionalCoordinates,
    fractional_difference_eq_iff d _ _ _ hd denominator lattice]
  constructor
  · rintro ⟨r, hr⟩ i
    exact ⟨r i, hr i⟩
  · intro h
    choose r hr using h
    exact ⟨r, hr⟩

/-- The executed numerator windows are faithful and complete representatives for the
fractional lattice quotient, for arbitrary denominator and lattice powers. -/
theorem reduce_window_eq_iff_fractional_congruence {rank : ℕ} (denominator lattice : ℕ)
    (d : CPolynomial K) (hd : d.toPoly.Monic) (p q : Fin rank → CPolynomial K) :
    reduceWindow (denominator + lattice) d p = reduceWindow (denominator + lattice) d q ↔
      PolynomialLatticeCongruent d.toPoly lattice
        (fractionalCoordinates d.toPoly denominator (fun i => (p i).toPoly))
        (fractionalCoordinates d.toPoly denominator (fun i => (q i).toPoly)) := by
  rw [reduce_window_eq_iff _ d hd,
    fractional_lattice_congruent_iff d.toPoly hd.ne_zero]

/-- The first window identifies fractions precisely modulo the original polynomial lattice. -/
theorem first_window_eq_iff {rank : ℕ} (d : CPolynomial K) (hd : d.toPoly.Monic)
    (p q : Fin rank → CPolynomial K) :
    firstWindow d p = firstWindow d q ↔
      PolynomialLatticeCongruent d.toPoly 0
        (fractionalCoordinates d.toPoly 1 (fun i => (p i).toPoly))
        (fractionalCoordinates d.toPoly 1 (fun i => (q i).toPoly)) :=
  reduce_window_eq_iff_fractional_congruence 1 0 d hd p q

/-- The second window identifies denominator-`d` fractions precisely modulo `dO`. -/
theorem second_window_eq_iff {rank : ℕ} (d : CPolynomial K) (hd : d.toPoly.Monic)
    (p q : Fin rank → CPolynomial K) :
    secondWindow d p = secondWindow d q ↔
      PolynomialLatticeCongruent d.toPoly 1
        (fractionalCoordinates d.toPoly 1 (fun i => (p i).toPoly))
        (fractionalCoordinates d.toPoly 1 (fun i => (q i).toPoly)) :=
  reduce_window_eq_iff_fractional_congruence 1 1 d hd p q

/-- The third window identifies denominator-`d²` fractions precisely modulo `dO`. -/
theorem third_window_eq_iff {rank : ℕ} (d : CPolynomial K) (hd : d.toPoly.Monic)
    (p q : Fin rank → CPolynomial K) :
    thirdWindow d p = thirdWindow d q ↔
      PolynomialLatticeCongruent d.toPoly 1
        (fractionalCoordinates d.toPoly 2 (fun i => (p i).toPoly))
        (fractionalCoordinates d.toPoly 2 (fun i => (q i).toPoly)) :=
  reduce_window_eq_iff_fractional_congruence 2 1 d hd p q

end Polynomial.FunctionFieldAlgorithms.CommonCenter
