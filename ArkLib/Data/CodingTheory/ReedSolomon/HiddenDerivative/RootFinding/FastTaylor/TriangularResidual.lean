/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.TriangularIdentity
public import ArkLib.Data.Polynomial.TruncatedSeries.Basic
public import ArkLib.ToCompPoly.Multivariate.PartialDerivative

/-!
# Executable shifted Taylor residual coefficients

The stored equation has variables `Z,Y₀,…,Yᵣ` and coefficient-ring arithmetic is
supplied directly. Shifting the original independent variable is an explicit
input preparation; no characteristic-dependent factorial division is used here.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.TriangularResidual

open CompPoly ArkLib.TruncatedSeries

variable {A : Type*} [CommRing A] [BEq A] [LawfulBEq A] [Nontrivial A] {r : ℕ}

/-- Store a completed coefficient list as a polynomial. -/
def polynomial (known : List A) : CPolynomial A :=
  ofCoeffs known.length (fun n => known.getD n 0)

omit [Nontrivial A] in
/-- The representation copies coefficients and is zero outside the list. -/
@[simp] theorem coeff_polynomial (known : List A) (n : ℕ) :
    (polynomial known).coeff n = known.getD n 0 := by
  rw [polynomial, coeff_ofCoeffs]
  split_ifs with h
  · rfl
  · exact (List.getD_eq_default _ _ (by omega)).symm

/-- The exact, division-free Hasse jet of the completed finite polynomial. -/
def jet (known : List A) : Fin (r + 2) → CPolynomial A :=
  Fin.cases CPolynomial.X (fun j => ofCoeffs known.length
    (fun n => ((n + j.val).choose j.val : A) * known.getD (n + j.val) 0))

/-- Exact polynomial semantics of the computed Hasse derivatives. -/
theorem jet_toPoly (known : List A) (i : Fin (r + 2)) :
    (jet known i).toPoly = Fin.cases Polynomial.X
      (fun j : Fin (r + 1) => Polynomial.hasseDeriv j.val (polynomial known).toPoly) i := by
  cases i using Fin.cases with
  | zero => exact CPolynomial.X_toPoly
  | succ j =>
    apply Polynomial.ext
    intro n
    rw [← CPolynomial.coeff_toPoly]
    change (ofCoeffs (A := A) known.length
      (fun n => ((n + j.val).choose j.val : A) * known.getD (n + j.val) 0)).coeff n = _
    rw [coeff_ofCoeffs, Fin.cases_succ, Polynomial.hasseDeriv_coeff, ← CPolynomial.coeff_toPoly,
      coeff_polynomial]
    split_ifs with hn
    · rfl
    · rw [List.getD_eq_default _ _ (by omega), mul_zero]

/-- Execute the stored equation on all Hasse-jet coordinates. -/
def residual (T : CPoly.CMvPolynomial (r + 2) A) (known : List A) : CPolynomial A :=
  T.eval₂ CPolynomial.CHom (jet known)

/-- The executable residual denotes the actual Hasse-jet substitution. -/
theorem residual_toPoly (T : CPoly.CMvPolynomial (r + 2) A) (known : List A) :
    (residual T known).toPoly =
      TriangularIdentity.residual (CPoly.fromCMvPolynomial T) (polynomial known).toPoly := by
  have hc : CPolynomial.ringEquiv.toRingHom.comp CPolynomial.CHom =
      (Polynomial.C : A →+* Polynomial A) := by
    apply RingHom.ext
    intro a
    simp [CPolynomial.ringEquiv_apply, CPolynomial.C_toPoly]
  rw [← CPolynomial.ringEquiv_apply]
  change CPolynomial.ringEquiv.toRingHom (residual T known) = _
  rw [residual, CPoly.eval₂_equiv, MvPolynomial.hom_eval₂, hc]
  have hj : (fun i => CPolynomial.ringEquiv.toRingHom (jet known i)) =
      Fin.cases Polynomial.X
        (fun j : Fin (r + 1) => Polynomial.hasseDeriv j.val (polynomial known).toPoly) := by
    funext i
    simpa [CPolynomial.ringEquiv_apply] using jet_toPoly known i
  rw [hj]
  rfl

/-- Compute the actual initial highest-variable partial. -/
def separant (T : CPoly.CMvPolynomial (r + 2) A) (known : List A) : A :=
  (CPoly.CMvPolynomial.partialDerivative (Fin.last (r + 1)) T).eval₂ (RingHom.id A)
    (Fin.cases 0 (fun j : Fin (r + 1) => known.getD j.val 0))

omit [Nontrivial A] in
/-- The stored partial derivative has the semantic separant value. -/
theorem separant_eq (T : CPoly.CMvPolynomial (r + 2) A) (known : List A) :
    separant T known = TriangularIdentity.separant (CPoly.fromCMvPolynomial T)
      (fun j : Fin (r + 1) => known.getD j.val 0) := by
  simp only [separant, CPoly.eval₂_equiv, CPoly.CMvPolynomial.fromCMvPolynomial_partialDerivative]
  rfl

omit [Nontrivial A] in
/-- Taking a list prefix agrees with the semantic coefficient-prefix polynomial. -/
theorem polynomial_take (known : List A) (l : ℕ) :
    (polynomial (known.take l)).toPoly =
      TriangularIdentity.prefixPolynomial (polynomial known).toPoly l := by
  apply Polynomial.ext
  intro n
  rw [← CPolynomial.coeff_toPoly, coeff_polynomial, TriangularIdentity.coeff_prefixPolynomial,
    ← CPolynomial.coeff_toPoly, coeff_polynomial]
  by_cases hn : n < l <;> simp [List.getD, hn]

/-- The executable residual's current coefficient has the binomial-times-separant slope. -/
theorem coefficient_affine (T : CPoly.CMvPolynomial (r + 2) A) (known : List A)
    (l : ℕ) (hl : r < l) :
    (residual T known).coeff (l - r) =
      (residual T (known.take l)).coeff (l - r) +
      ((l.choose r : A) * known.getD l 0) * separant T known := by
  rw [CPolynomial.coeff_toPoly, residual_toPoly,
    TriangularIdentity.coefficient_affine _ _ l hl, ← polynomial_take,
    ← residual_toPoly, ← CPolynomial.coeff_toPoly,
    ← CPolynomial.coeff_toPoly, coeff_polynomial, separant_eq]
  congr 2
  congr 1
  funext j
  rw [← CPolynomial.coeff_toPoly, coeff_polynomial]

/-- A residual's constant coefficient is evaluation on the initial coefficient vector. -/
theorem residual_constant (T : CPoly.CMvPolynomial (r + 2) A) (known : List A) :
    (residual T known).coeff 0 = T.eval₂ (RingHom.id A)
      (Fin.cases 0 (fun j : Fin (r + 1) => known.getD j.val 0)) := by
  let phi : CPolynomial A →+* A := Polynomial.constantCoeff.comp CPolynomial.ringEquiv.toRingHom
  have hphi (p : CPolynomial A) : phi p = p.coeff 0 := by
    simpa [phi, CPolynomial.ringEquiv_apply] using (CPolynomial.coeff_toPoly p 0).symm
  have hc : phi.comp CPolynomial.CHom = RingHom.id A := by
    ext a
    rw [RingHom.comp_apply, hphi]
    simp [CPolynomial.coeff_C]
  rw [← hphi, residual, CPoly.eval₂_equiv, MvPolynomial.hom_eval₂, hc, CPoly.eval₂_equiv]
  congr 1
  funext i
  rw [hphi]
  cases i using Fin.cases with
  | zero =>
    rw [jet, Fin.cases_zero, CPolynomial.coeff_toPoly, CPolynomial.X_toPoly]
    simp
  | succ j =>
    simp only [jet, Fin.cases_succ, coeff_ofCoeffs, Nat.zero_add, Nat.choose_self,
      Nat.cast_one, one_mul]
    split_ifs with h
    · rfl
    · exact (List.getD_eq_default _ _ (by omega)).symm

end ReedSolomon.HiddenDerivative.FastTaylor.TriangularResidual
