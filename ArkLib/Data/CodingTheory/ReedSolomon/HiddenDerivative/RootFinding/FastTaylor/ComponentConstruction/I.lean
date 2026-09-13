/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Constructor
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.RegularPart

/-!
# Computed first-order regular components for fast Taylor charts

This adapter specializes an actual first-order differential equation at the chosen center and
feeds its literal highest-jet partial to the generic bivariate regular-part producer.  Its coverage
theorem is per stage and center and applies to every extension-field point, including regular
points over ramified projection fibers.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction.FirstOrder

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open Polynomial.FunctionFieldAlgorithms.BivariateReducedSupport

variable {E : Type*} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E]

/-- The actual specialized first-order equation in stored bivariate form, with coordinates
`[u₀,u₁]`. -/
def specializedEquation (center : E) (T : CMvPolynomial 3 E) : CBivariate E :=
  fromOrdinaryCMv (FastTaylor.initialEquation center T)

/-- The actual specialized highest-jet partial in the same bivariate coordinates. -/
def specializedSeparant (center : E) (T : CMvPolynomial 3 E) : CBivariate E :=
  fromOrdinaryCMv (FastTaylor.initialSeparant center T)

/-- Execute radicalization, actual-separant gcd removal, and checked exact division for one
first-order stage and center. -/
def run (p : ℕ) (inverse : E → E) (center : E) (T : CMvPolynomial 3 E) :
    RegularPart.Result E :=
  RegularPart.run p inverse (specializedEquation center T) (specializedSeparant center T)

/-- The returned regular union in the compact multivariate representation consumed by the
first-order Taylor chart constructor. -/
def component (data : RegularPart.Data E) : CMvPolynomial 2 E :=
  CBivariate.toOrdinaryCMv data.regular

omit [DecidableEq E] in
/-- Converting the constructor-facing component back to the certified bivariate representation
recovers the exact polynomial produced by radicalization and separant removal. -/
theorem fromOrdinaryCMv_component (data : RegularPart.Data E) :
    fromOrdinaryCMv (component data) = data.regular :=
  fromOrdinaryCMv_toOrdinaryCMv data.regular

private noncomputable def nestedScalarHom : E →+* Polynomial (Polynomial E) :=
  (Polynomial.C : Polynomial E →+* Polynomial (Polynomial E)).comp
    (Polynomial.C : E →+* Polynomial E)

private noncomputable def nestedVariables : Fin 2 → Polynomial (Polynomial E) :=
  ![Polynomial.C Polynomial.X, Polynomial.X]

omit [DecidableEq E] in
private theorem toPoly_fromOrdinaryCMv (Q : CMvPolynomial 2 E) :
    CBivariate.toPoly (fromOrdinaryCMv Q) =
      MvPolynomial.eval₂ nestedScalarHom nestedVariables (fromCMvPolynomial Q) := by
  classical
  let h := CBivariate.toPolyRingHom (R := E)
  have heq := MvPolynomial.eval₂_comp_left h
    (CHom.comp CHom) ![CPolynomial.C CPolynomial.X, CPolynomial.X]
    (fromCMvPolynomial Q)
  rw [fromOrdinaryCMv, CPoly.eval₂_equiv]
  change h _ = _
  rw [heq]
  congr 1
  · ext a
    simp [h, nestedScalarHom, CBivariate.toPolyRingHom, CBivariate.ringEquiv,
      CBivariate.toPoly_eq_map, CPolynomial.C_toPoly]
  · funext i
    fin_cases i <;>
      simp [h, nestedVariables, CBivariate.toPolyRingHom, CBivariate.ringEquiv,
        CBivariate.toPoly_eq_map, CPolynomial.C_toPoly, CPolynomial.X_toPoly]

omit [DecidableEq E] [BEq E] [LawfulBEq E] in
private theorem derivative_nested_eval (Q : MvPolynomial (Fin 2) E) :
    Polynomial.derivative (MvPolynomial.eval₂ nestedScalarHom nestedVariables Q) =
      MvPolynomial.eval₂ nestedScalarHom nestedVariables
        (MvPolynomial.pderiv (1 : Fin 2) Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simp [nestedScalarHom]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      fin_cases i <;>
        simp [nestedVariables] at hP ⊢ <;>
        simp [hP, mul_comm, add_comm]

omit [DecidableEq E] in
/-- Ordinary stored conversion sends partial differentiation in coordinate one to the outer
bivariate derivative. -/
theorem fromOrdinaryCMv_partialDerivative_one (Q : CMvPolynomial 2 E) :
    fromOrdinaryCMv (CMvPolynomial.partialDerivative (1 : Fin 2) Q) =
      CBivariate.partialDerivY (fromOrdinaryCMv Q) := by
  classical
  apply CBivariate.ringEquiv.injective
  have h :
      CBivariate.toPoly (fromOrdinaryCMv (CMvPolynomial.partialDerivative (1 : Fin 2) Q)) =
        CBivariate.toPoly (CBivariate.partialDerivY (fromOrdinaryCMv Q)) := by
    rw [CBivariate.partialDerivY_toPoly, toPoly_fromOrdinaryCMv,
      toPoly_fromOrdinaryCMv, CMvPolynomial.fromCMvPolynomial_partialDerivative]
    exact (derivative_nested_eval (fromCMvPolynomial Q)).symm
  exact h

/-- The supplied separant is literally the outer derivative of the supplied specialized
first-order equation. -/
theorem specializedSeparant_eq_partialDerivY (center : E) (T : CMvPolynomial 3 E) :
    specializedSeparant center T = CBivariate.partialDerivY (specializedEquation center T) := by
  have hconcrete : FastTaylor.initialSeparant center T =
      CMvPolynomial.partialDerivative (1 : Fin 2) (FastTaylor.initialEquation center T) := by
    apply fromCMvPolynomial_injective
    rw [CMvPolynomial.fromCMvPolynomial_partialDerivative,
      FastTaylor.initialEquation_semantics, FastTaylor.initialSeparant_semantics]
    exact (ReedSolomon.HiddenDerivative.pderiv_initialJetEquation center
      (ReedSolomon.HiddenDerivative.semanticEquation T) (Fin.last 1)).symm
  rw [specializedSeparant, specializedEquation, hconcrete,
    fromOrdinaryCMv_partialDerivative_one]

/-- Under the real positive-characteristic inverse-Frobenius hypothesis, the actual first-order
producer cannot reach an arithmetic failure. -/
theorem run_success (p : ℕ) [Fact p.Prime] [CharP E p] (inverse : E → E)
    (center : E) (T : CMvPolynomial 3 E)
    (hequation : specializedEquation center T ≠ 0)
    (hinverse : p ≤
        (ClearDenominators.primitivePart (specializedEquation center T)).natDegree →
      ∀ a, inverse a ^ p = a) :
    (∃ data, run p inverse center T = .emptyRegularPart data) ∨
      (∃ data, run p inverse center T = .regularPart data) := by
  exact RegularPart.run_success p inverse _ _ hequation hinverse

/-- Every returned nonconstant first-order component has the complete generic producer
certificate for the actual specialized equation and separant. -/
theorem run_regularPart_certificate (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (center : E) (T : CMvPolynomial 3 E)
    (data : RegularPart.Data E)
    (hinverse : p ≤
        (ClearDenominators.primitivePart (specializedEquation center T)).natDegree →
      ∀ a, inverse a ^ p = a)
    (hrun : run p inverse center T = .regularPart data) :
    RegularPart.Certificate p inverse (specializedEquation center T)
      (specializedSeparant center T) data :=
  RegularPart.run_regularPart_certificate p inverse _ _ data hinverse hrun

/-- A constructor-facing component returned by the actual producer is squarefree over the
function field in the first jet coordinate. -/
theorem run_component_squarefree (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (center : E) (T : CMvPolynomial 3 E)
    (data : RegularPart.Data E)
    (hinverse : p ≤
        (ClearDenominators.primitivePart (specializedEquation center T)).natDegree →
      ∀ a, inverse a ^ p = a)
    (hrun : run p inverse center T = .regularPart data) :
    Squarefree (ClearDenominators.valueGlobal data.regular) :=
  (run_regularPart_certificate p inverse center T data hinverse hrun).regular_squarefree_valueGlobal

/-- Every regular root of the actual specialized stage equation lies on the returned component.
There is no unramified-projection, denominator, or discriminant premise. -/
theorem run_regularPart_covers
    (p : ℕ) [Fact p.Prime] [CharP E p] (inverse : E → E)
    (center : E) (T : CMvPolynomial 3 E) (data : RegularPart.Data E)
    (hinverse : p ≤
        (ClearDenominators.primitivePart (specializedEquation center T)).natDegree →
      ∀ a, inverse a ^ p = a)
    (hrun : run p inverse center T = .regularPart data)
    {K : Type*} [Field K] (embedding : E →+* K) (u₀ u₁ : K)
    (hequation : RegularPart.evalAt embedding u₀ u₁ (specializedEquation center T) = 0)
    (hseparant : RegularPart.evalAt embedding u₀ u₁
      (specializedSeparant center T) ≠ 0) :
    RegularPart.evalAt embedding u₀ u₁ data.regular = 0 := by
  have cert := run_regularPart_certificate p inverse center T data hinverse hrun
  exact cert.evalAt_regular_of_equation embedding u₀ u₁
    (specializedSeparant_eq_partialDerivY center T) hequation hseparant

/-- If the actual producer returns the empty branch, the specialized equation has no regular
root over any extension field. -/
theorem run_emptyRegularPart_no_regular_root
    (p : ℕ) [Fact p.Prime] [CharP E p] (inverse : E → E)
    (center : E) (T : CMvPolynomial 3 E) (data : RegularPart.Data E)
    (hequation : specializedEquation center T ≠ 0)
    (hinverse : p ≤
        (ClearDenominators.primitivePart (specializedEquation center T)).natDegree →
      ∀ a, inverse a ^ p = a)
    (hrun : run p inverse center T = .emptyRegularPart data)
    {K : Type*} [Field K] (embedding : E →+* K) (u₀ u₁ : K) :
    ¬ (RegularPart.evalAt embedding u₀ u₁ (specializedEquation center T) = 0 ∧
      RegularPart.evalAt embedding u₀ u₁ (specializedSeparant center T) ≠ 0) := by
  exact RegularPart.run_emptyRegularPart_no_regular_point p inverse _ _ data hequation hinverse
    (specializedSeparant_eq_partialDerivY center T) hrun embedding u₀ u₁

end ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction.FirstOrder

end
