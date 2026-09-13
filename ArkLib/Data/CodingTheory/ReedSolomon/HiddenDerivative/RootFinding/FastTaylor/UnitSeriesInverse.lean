/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.TruncatedSeries.Basic
public import ArkLib.Data.Polynomial.NewtonInverse

/-!
# Finite unit-series inversion over a supplied coefficient ring

This intermediate backend uses the verified Newton iteration and truncates its
output. Its input includes the actual unit constant coefficient. It does not
introduce an inverse coordinate in a differential system or assert relaxed-cost
parity.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.UnitSeriesInverse

open CompPoly ArkLib.TruncatedSeries

variable {A : Type*} [CommRing A] [BEq A] [LawfulBEq A] [Nontrivial A]

/-- Compute a finite inverse from a supplied unit constant coefficient. -/
def compute (k : ℕ) (p : CPolynomial A) (u : Aˣ) : CPolynomial A :=
  truncate k (Polynomial.NewtonInverse.correct k p (CPolynomial.C (↑u⁻¹ : A)))

/-- The arithmetic inverse is correct to exactly the requested finite precision. -/
theorem compute_sound (k : ℕ) (p : CPolynomial A) (u : Aˣ)
    (hu : p.coeff 0 = (u : A)) : LowEq k (p * compute k p u) 1 := by
  have he : Order 1 (1 - p * CPolynomial.C (↑u⁻¹ : A)) := by
    intro i hi
    have : i = 0 := by omega
    subst i
    simp [CPolynomial.coeff_sub, CPolynomial.coeff_mul, CPolynomial.coeff_C,
      CPolynomial.coeff_one, CPolynomial.coeff_zero, hu]
  have hp := (he.pow (2 ^ Polynomial.NewtonInverse.rounds k)).mono
    (by simpa using Polynomial.NewtonInverse.precision_le k)
  rw [← Polynomial.NewtonInverse.residual_correct] at hp
  have hcorrect : LowEq k
      (p * Polynomial.NewtonInverse.correct k p (CPolynomial.C (↑u⁻¹ : A))) 1 := by
    intro i hi
    have h := hp i hi
    simp only [CPolynomial.coeff_sub, CPolynomial.coeff_zero] at h
    exact (sub_eq_zero.mp h).symm
  exact ((LowEq.refl k p).mul (truncate_lowEq k _)).trans hcorrect

/-- Newton arithmetic preserves equality below any stated precision. -/
theorem iterate_lowEq (rounds m : ℕ) (p q b c : CPolynomial A)
    (hp : LowEq m p q) (hb : LowEq m b c) :
    LowEq m (Polynomial.NewtonInverse.iterate rounds p b)
      (Polynomial.NewtonInverse.iterate rounds q c) := by
  induction rounds with
  | zero => exact hb
  | succ n ih =>
    exact ih.mul ((LowEq.refl m 2).sub (hp.mul ih))

/-- Coefficients of the inverse depend only on the corresponding input prefix. -/
theorem compute_lowEq (k m : ℕ) (p q : CPolynomial A) (u : Aˣ)
    (hm : m ≤ k) (hp : LowEq m p q) :
    LowEq m (compute k p u) (compute k q u) := by
  unfold compute Polynomial.NewtonInverse.correct
  exact ((truncate_lowEq k _).mono hm).trans
    ((iterate_lowEq _ m p q _ _ hp (LowEq.refl m _)).trans
      ((truncate_lowEq k _).mono hm).symm)

end ReedSolomon.HiddenDerivative.FastTaylor.UnitSeriesInverse
