/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Validity
public import ArkLib.Data.MvPolynomial.TaylorReconstruction.UnivariateView
public import ArkLib.Data.Polynomial.ConfluentAlgebra.Structure

/-!
# Executable bivariate view of a first-order Taylor chart

The first-order norm algorithm treats the two chart variables as `U` and `V`, with `V` the
monic fiber variable.  This module converts the stored `CMvPolynomial 2` chart payload to the
nested representation `CPolynomial (CPolynomial E)` used by norms and finite towers.  Both
conversions are executable evaluations of stored polynomials; no root extraction is involved.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer.ChartPolynomials

open CompPoly CPoly CPoly.TaylorReconstruction
open ReedSolomon.HiddenDerivative.FastTaylor
open ArkLib.ConfluentAlgebra

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Convert the single free chart variable to a stored univariate polynomial. -/
def coefficientPolynomial : CMvPolynomial 1 E →+* CPolynomial E :=
  CMvPolynomial.eval₂Hom CPolynomial.CHom (fun _ => CPolynomial.X)

/-- Convert `[U,V]` to a polynomial in `V` with coefficients in `E[U]`. -/
def bivariatePolynomial : CMvPolynomial 2 E →+* CPolynomial (CPolynomial E) :=
  CMvPolynomial.eval₂Hom (CPolynomial.CHom.comp CPolynomial.CHom)
    ![CPolynomial.C CPolynomial.X, CPolynomial.X]

private theorem storedMv_hom_ext {A : Type*} [CommSemiring A] {n : ℕ}
    (f g : CMvPolynomial n E →+* A)
    (hC : ∀ a, f (CMvPolynomial.C a) = g (CMvPolynomial.C a))
    (hX : ∀ i, f (CMvPolynomial.X i) = g (CMvPolynomial.X i)) : f = g := by
  have hc (a : E) : polyRingEquiv.symm (MvPolynomial.C a) =
      (CMvPolynomial.C a : CMvPolynomial n E) := by
    apply polyRingEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    exact (CMvPolynomial.fromCMvPolynomial_C a).symm
  have hx (i : Fin n) : polyRingEquiv.symm (MvPolynomial.X i) =
      (CMvPolynomial.X i : CMvPolynomial n E) := by
    apply polyRingEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    exact (CMvPolynomial.fromCMvPolynomial_X i).symm
  have h : f.comp polyRingEquiv.symm.toRingHom = g.comp polyRingEquiv.symm.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa [hc] using hC a
    · intro i
      simpa [hx] using hX i
  ext p
  simpa using RingHom.congr_fun h (polyRingEquiv p)

/-- Direct bivariate conversion is coefficient base change of the constructor's last-variable
view.  This connects the executable norm representation to `ChartData.NormalForms`. -/
theorem bivariatePolynomial_eq_mapCoefficients [DecidableEq E] (p : CMvPolynomial 2 E) :
    bivariatePolynomial p = mapCoefficients coefficientPolynomial (splitLast p) := by
  change bivariatePolynomial p =
    ((mapCoefficientsHom (coefficientPolynomial (E := E))).comp
      (splitLast (E := E) (r := 1))) p
  have hhom : bivariatePolynomial =
      (mapCoefficientsHom (coefficientPolynomial (E := E))).comp
        (splitLast (E := E) (r := 1)) := by
    apply storedMv_hom_ext
    · intro a
      apply CPolynomial.toPoly_injective
      change (bivariatePolynomial (CMvPolynomial.C a)).toPoly =
        (mapCoefficients (coefficientPolynomial (E := E))
          (splitLast (E := E) (r := 1) (CMvPolynomial.C a))).toPoly
      rw [toPoly_mapCoefficients]
      simp [bivariatePolynomial, coefficientPolynomial, CMvPolynomial.eval₂Hom_apply, eval₂_equiv,
        CMvPolynomial.fromCMvPolynomial_C, CPolynomial.C_toPoly]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · apply CPolynomial.toPoly_injective
        change (bivariatePolynomial (CMvPolynomial.X (Fin.last 1))).toPoly =
          (mapCoefficients (coefficientPolynomial (E := E))
            (splitLast (E := E) (r := 1) (CMvPolynomial.X (Fin.last 1)))).toPoly
        rw [toPoly_mapCoefficients, splitLast_X_last]
        simp [bivariatePolynomial, coefficientPolynomial, CMvPolynomial.eval₂Hom_apply, eval₂_equiv,
          CMvPolynomial.fromCMvPolynomial_X, CPolynomial.X_toPoly]
      · apply CPolynomial.toPoly_injective
        change (bivariatePolynomial (CMvPolynomial.X j.castSucc)).toPoly =
          (mapCoefficients (coefficientPolynomial (E := E))
            (splitLast (E := E) (r := 1) (CMvPolynomial.X j.castSucc))).toPoly
        rw [toPoly_mapCoefficients, splitLast_X_castSucc]
        fin_cases j
        simp [bivariatePolynomial, coefficientPolynomial, CMvPolynomial.eval₂Hom_apply,
          eval₂_equiv, CMvPolynomial.fromCMvPolynomial_X, CPolynomial.C_toPoly]
  exact RingHom.congr_fun hhom p

/-- The nested equation, separant, common denominator, numerators and agreement rows derived
definitionally from one first-order chart. -/
structure Data (E : Type*) [Field E] [BEq E] [LawfulBEq E] (k : ℕ) where
  equation : CPolynomial (CPolynomial E)
  separant : CPolynomial (CPolynomial E)
  denominator : CPolynomial (CPolynomial E)
  numerators : Fin k → CPolynomial (CPolynomial E)

/-- Convert every polynomial needed by the first-order candidate producer. -/
def ofChart {k : ℕ} (chart : ChartData E 1 k) : Data E k :=
  { equation := bivariatePolynomial chart.equation
    separant := bivariatePolynomial chart.separant
    denominator := bivariatePolynomial chart.denominator
    numerators := fun j => bivariatePolynomial (chart.numerators j) }

/-- The existing chart normal-form certificate supplies monicity in the exact nested
representation consumed by component descent and norms. -/
theorem equation_monic_of_normalForms [DecidableEq E] {k b L : ℕ} (chart : ChartData E 1 k)
    (hnormal : chart.NormalForms b L) : (ofChart chart).equation.monic := by
  rw [show (ofChart chart).equation =
      mapCoefficients coefficientPolynomial (splitLast chart.equation) by
    exact bivariatePolynomial_eq_mapCoefficients chart.equation]
  exact monic_mapCoefficients coefficientPolynomial (splitLast chart.equation) hnormal.1

/-- Convert an executed chart agreement row to the same nested representation. -/
def agreement {k : ℕ} (chart : ChartData E 1 k) (alpha received : E) :
    CPolynomial (CPolynomial E) :=
  bivariatePolynomial (chart.agreement alpha received)

@[simp] theorem bivariatePolynomial_chart_agreement {k : ℕ} (chart : ChartData E 1 k)
    (alpha received : E) :
    bivariatePolynomial (chart.agreement alpha received) = agreement chart alpha received := rfl

/-- The conversion preserves the exact stored chart equation; flattening the intermediate
last-variable view gives the original polynomial before coefficient conversion. -/
theorem splitLast_chart_equation [DecidableEq E] {k : ℕ} (chart : ChartData E 1 k) :
    flattenLast (splitLast chart.equation) = chart.equation := by
  simp

end ReedSolomon.ListDecoding.FirstOrderNormProducer.ChartPolynomials
