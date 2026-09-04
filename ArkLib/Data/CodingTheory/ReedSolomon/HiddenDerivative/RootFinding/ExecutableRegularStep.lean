/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.RegularLifting
import CompPoly.Multivariate.MvPolyEquiv.Eval
import CompPoly.Univariate.ToPoly.Impl

/-!
# Executable regular coefficient lifting

This file gives a computable version of one regular coefficient-lifting step. A candidate is
stored in coordinates centered at the lifting point, as a `CompPoly.CPolynomial`. The differential
equation is a `CPoly.CMvPolynomial` whose variables are ordered as `X, Y₀, ..., Y_r`. The step
enumerates only the finite base field and retains exactly the coefficients whose next differential
residual coefficient vanishes.

The semantic bridge maps the concrete representations to the shifted-jet presentation used by
`RegularLifting`. No polynomial equality or divisibility test occurs in the executable kernel.
-/

namespace ReedSolomon.HiddenDerivative

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Concrete representations -/

/-- Interpret concrete variables `0, 1, ..., r+1` as `X, Y₀, ..., Y_r`. -/
def finToJetVariable (r : ℕ) : Fin (r + 2) → JetVariable r :=
  Fin.cases none some

/-- Mathematical differential polynomial denoted by a concrete differential equation. -/
noncomputable def semanticEquation {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) :
    DifferentialPolynomial F r :=
  MvPolynomial.rename (finToJetVariable r) (CPoly.fromCMvPolynomial Q)

/-- Interpret a centered coefficient polynomial as an ordinary polynomial in the original
coordinate. -/
noncomputable def unshift (center : F) (P : CompPoly.CPolynomial F) : F[X] :=
  Polynomial.taylor (-center) P.toPoly

/-- The constant-polynomial embedding into computable univariate polynomials. -/
def cPolynomialCHom : F →+* CompPoly.CPolynomial F where
  toFun := CompPoly.CPolynomial.C
  map_one' := by
    apply CompPoly.CPolynomial.ringEquiv.injective
    simp only [CompPoly.CPolynomial.ringEquiv_apply, CompPoly.CPolynomial.C_toPoly,
      map_one]
  map_mul' a b := by
    apply CompPoly.CPolynomial.ringEquiv.injective
    simp only [CompPoly.CPolynomial.ringEquiv_apply, CompPoly.CPolynomial.C_toPoly,
      map_mul]
  map_zero' := by
    apply CompPoly.CPolynomial.ringEquiv.injective
    simp only [CompPoly.CPolynomial.ringEquiv_apply, CompPoly.CPolynomial.C_toPoly,
      map_zero]
  map_add' a b := by
    apply CompPoly.CPolynomial.ringEquiv.injective
    simp only [CompPoly.CPolynomial.ringEquiv_apply, CompPoly.CPolynomial.C_toPoly,
      map_add]

/-- Semantic ring homomorphism from computable to Mathlib polynomials. -/
noncomputable def cPolynomialToPolyHom : CompPoly.CPolynomial F →+* F[X] :=
  CompPoly.CPolynomial.ringEquiv.toRingHom

@[simp]
theorem cPolynomialToPolyHom_apply (P : CompPoly.CPolynomial F) :
    cPolynomialToPolyHom P = P.toPoly :=
  rfl

/-- Hasse derivative on a centered coefficient array. Keeping the source array length makes the
coefficient formula direct; `ofArray` removes the trailing zero coefficients. -/
def centeredHasseDeriv (j : ℕ) (P : CompPoly.CPolynomial F) :
    CompPoly.CPolynomial F :=
  CompPoly.CPolynomial.ofArray <|
    Array.ofFn (n := P.val.size) fun i =>
      ((i.val + j).choose j : F) * P.coeff (i.val + j)

/-- Concrete shifted values for `X, Y₀, ..., Y_r`. -/
def centeredJetValues {r : ℕ} (center : F) (P : CompPoly.CPolynomial F) :
    Fin (r + 2) → CompPoly.CPolynomial F :=
  Fin.cases (CompPoly.CPolynomial.C center + CompPoly.CPolynomial.X)
    (fun j => centeredHasseDeriv j.val P)

/-- Add the next centered candidate coefficient. -/
def effectiveRegularCandidate (k r : ℕ) (P : CompPoly.CPolynomial F) (gamma : F) :
    CompPoly.CPolynomial F :=
  P + CompPoly.CPolynomial.monomial (k + r) gamma

/-- Compute the full shifted differential residual of a centered candidate. -/
def effectiveResidual {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CompPoly.CPolynomial F) : CompPoly.CPolynomial F :=
  Q.eval₂ cPolynomialCHom (centeredJetValues center P)

/-- Compute the first unresolved residual coefficient after adding `gamma`. -/
def effectiveResidualCoeff {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CompPoly.CPolynomial F) (k : ℕ) (gamma : F) : F :=
  (effectiveResidual Q center (effectiveRegularCandidate k r P gamma)).coeff k

/-- Enumerate the base-field coefficients that make the next residual coefficient vanish. -/
def effectiveRegularCoefficients {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CompPoly.CPolynomial F) (k : ℕ) : Finset F :=
  Finset.univ.filter fun gamma => effectiveResidualCoeff Q center P k gamma = 0

/-! ### Representation equations -/

theorem coeff_centeredHasseDeriv (j : ℕ) (P : CompPoly.CPolynomial F) (i : ℕ) :
    (centeredHasseDeriv j P).coeff i =
      ((i + j).choose j : F) * P.coeff (i + j) := by
  rw [centeredHasseDeriv, CompPoly.CPolynomial.coeff_ofArray]
  by_cases hi : i < P.val.size
  · simp [Array.getD, hi]
  · have hij : P.val.size ≤ i + j := (Nat.le_of_not_gt hi).trans (Nat.le_add_right i j)
    simp [Array.getD, hi, CompPoly.CPolynomial.coeff,
      CompPoly.CPolynomial.Raw.coeff, hij]

@[simp]
theorem centeredHasseDeriv_toPoly (j : ℕ) (P : CompPoly.CPolynomial F) :
    (centeredHasseDeriv j P).toPoly = Polynomial.hasseDeriv j P.toPoly := by
  ext i
  rw [← CompPoly.CPolynomial.coeff_toPoly, coeff_centeredHasseDeriv,
    Polynomial.hasseDeriv_coeff, CompPoly.CPolynomial.coeff_toPoly]

@[simp]
theorem effectiveRegularCandidate_toPoly (k r : ℕ) (P : CompPoly.CPolynomial F) (gamma : F) :
    (effectiveRegularCandidate k r P gamma).toPoly =
      P.toPoly + Polynomial.monomial (k + r) gamma := by
  rw [effectiveRegularCandidate, CompPoly.CPolynomial.toPoly_add,
    CompPoly.CPolynomial.monomial_toPoly]

theorem coeff_effectiveRegularCandidate (k r : ℕ) (P : CompPoly.CPolynomial F)
    (gamma : F) (i : ℕ) :
    (effectiveRegularCandidate k r P gamma).coeff i =
      P.coeff i + if i = k + r then gamma else 0 := by
  rw [effectiveRegularCandidate, CompPoly.CPolynomial.coeff_add,
    CompPoly.CPolynomial.coeff_monomial]

theorem unshift_effectiveRegularCandidate (center gamma : F) (k r : ℕ)
    (P : CompPoly.CPolynomial F) :
    unshift center (effectiveRegularCandidate k r P gamma) =
      regularLiftCandidate center gamma k r (unshift center P) := by
  rw [unshift, unshift, effectiveRegularCandidate_toPoly]
  simp only [map_add, Polynomial.taylor_monomial, regularLiftCandidate, hassePerturbation]
  congr 2
  rw [Polynomial.C_neg, sub_eq_add_neg]

theorem centeredJetValues_toPoly {r : ℕ} (center : F) (P : CompPoly.CPolynomial F)
    (v : Fin (r + 2)) :
    (centeredJetValues center P v).toPoly =
      match finToJetVariable r v with
      | none => Polynomial.C center + Polynomial.X
      | some j => Polynomial.taylor center (Polynomial.hasseDeriv j.val (unshift center P)) := by
  cases v using Fin.cases with
  | zero =>
      change (CompPoly.CPolynomial.C center + CompPoly.CPolynomial.X).toPoly =
        Polynomial.C center + Polynomial.X
      rw [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.C_toPoly,
        CompPoly.CPolynomial.X_toPoly]
  | succ j =>
      change (centeredHasseDeriv j.val P).toPoly =
        Polynomial.taylor center (Polynomial.hasseDeriv j.val (unshift center P))
      rw [centeredHasseDeriv_toPoly, unshift, Polynomial.hasseDeriv_taylor,
        Polynomial.taylor_taylor, add_neg_cancel, Polynomial.taylor_zero]

/-- The computable residual denotes the existing shifted differential specialization. -/
theorem effectiveResidual_toPoly {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CompPoly.CPolynomial F) :
    (effectiveResidual Q center P).toPoly =
      shiftedJetSubstitution center (unshift center P) (semanticEquation Q) := by
  rw [← cPolynomialToPolyHom_apply]
  rw [effectiveResidual, CPoly.eval₂_equiv]
  change cPolynomialToPolyHom
    (MvPolynomial.eval₂Hom cPolynomialCHom (centeredJetValues center P)
      (CPoly.fromCMvPolynomial Q)) = _
  calc
    _ = MvPolynomial.eval₂Hom
          (cPolynomialToPolyHom.comp cPolynomialCHom)
          (fun v => cPolynomialToPolyHom (centeredJetValues center P v))
          (CPoly.fromCMvPolynomial Q) :=
      MvPolynomial.map_eval₂Hom
        (R := F) (S₁ := CompPoly.CPolynomial F) (S₂ := F[X]) (σ := Fin (r + 2))
        cPolynomialCHom (centeredJetValues center P) cPolynomialToPolyHom
        (CPoly.fromCMvPolynomial Q)
    _ = shiftedJetSubstitution center (unshift center P) (semanticEquation Q) := by
      rw [semanticEquation, shiftedJetSubstitution, MvPolynomial.aeval_def,
        MvPolynomial.eval₂_rename]
      change MvPolynomial.eval₂Hom
          (cPolynomialToPolyHom.comp cPolynomialCHom)
          (fun v => cPolynomialToPolyHom (centeredJetValues center P v))
          (CPoly.fromCMvPolynomial Q) =
        MvPolynomial.eval₂Hom (algebraMap F F[X])
          ((fun v : JetVariable r => match v with
            | none => Polynomial.C center + Polynomial.X
            | some j => Polynomial.taylor center
                (Polynomial.hasseDeriv j.val (unshift center P))) ∘ finToJetVariable r)
          (CPoly.fromCMvPolynomial Q)
      apply MvPolynomial.eval₂Hom_congr
      · ext x n
        change (CompPoly.CPolynomial.C x).toPoly.coeff n = (Polynomial.C x).coeff n
        rw [CompPoly.CPolynomial.C_toPoly]
      · funext v
        exact centeredJetValues_toPoly center P v
      · rfl

@[simp]
theorem mem_effectiveRegularCoefficients {r : ℕ}
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CompPoly.CPolynomial F) (k : ℕ) (gamma : F) :
    gamma ∈ effectiveRegularCoefficients Q center P k ↔
      effectiveResidualCoeff Q center P k gamma = 0 := by
  simp only [effectiveRegularCoefficients, Finset.mem_filter, Finset.mem_univ, true_and]

end ReedSolomon.HiddenDerivative
