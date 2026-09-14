/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Constructor
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.TriangularPreparation

/-!
# Checked recurrence preparation in a computed Taylor chart

The component equation and the actual local separant inverse discharge the checked
preparation conditions. This adapter leaves the existing Newton constructor unchanged.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.TriangularPreparation

open CompPoly CPoly CPoly.TaylorReconstruction ArkLib.ConfluentAlgebra

variable {E : Type*} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E] {r : ℕ}

/-- The original component equation supplies the initial-root certificate for preparation. -/
theorem local_initial_zero (N : ℕ) [Fact (0 < N)]
    (component : CMvPolynomial (r + 1) E) (values : List E)
    (g : Geometry.MonicProjection.Data r E)
    (hg : Geometry.MonicProjection.construct? component values = some g)
    [Fact (splitLast g.polynomial).monic]
    (a : Fin r → E) (center : E) (T : CMvPolynomial (r + 2) E)
    (hdvd : component ∣ initialEquation center T) :
    T.eval₂ (SeriesNewton.scalarHom (localEquation N a g.polynomial))
      (Fin.cases (SeriesNewton.scalarHom (localEquation N a g.polynomial) center)
        (localInitialJet N g.polynomial a g.forward)) = 0 := by
  rw [← eval₂_initialEquation, eval₂_equiv, ← local_project_eq_eval]
  exact local_component_multiple_zero N component (initialEquation center T) values g hg a hdvd

/-- The separant checked by preparation is exactly the chart's stored local separant. -/
theorem local_separant (N : ℕ) [Fact (0 < N)]
    (equation : CMvPolynomial (r + 1) E) [Fact (splitLast equation).monic]
    [Fact (0 < (splitLast equation).toPoly.degree)]
    (a : Fin r → E) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (center : E) (T : CMvPolynomial (r + 2) E) :
    TriangularResidual.separant
      (shiftEquation (SeriesNewton.scalarHom (localEquation N a equation)) center T)
      (List.ofFn (localInitialJet N equation a M)) =
      ConfluentSample.localSeparant N equation
        (Geometry.projectPolynomial M (initialSeparant center T)) a := by
  rw [separant_shiftEquation]
  have hcoords : (fun j : Fin (r + 1) =>
      (List.ofFn (localInitialJet N equation a M)).getD j.val 0) =
      localInitialJet N equation a M := by
    funext j
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt), List.getElem_ofFn]
  rw [hcoords, ← eval₂_initialSeparant, ConfluentSample.localSeparant,
    local_project_eq_eval, ← eval₂_equiv]

/-- Computed chart geometry, component divisibility and the computed inverse suffice for
checked preparation. No root or binomial-unit oracle is an additional hypothesis. -/
theorem prepare?_exists_of_component (N p k : ℕ) [Fact (0 < N)] [CharP E p]
    (component : CMvPolynomial (r + 1) E) (values : List E)
    (g : Geometry.MonicProjection.Data r E)
    (hg : Geometry.MonicProjection.construct? component values = some g)
    [Fact (splitLast g.polynomial).monic]
    [Fact (0 < (splitLast g.polynomial).toPoly.degree)]
    (a : Fin r → E) (center : E) (T : CMvPolynomial (r + 2) E)
    (hrk : r < k) (hkp : k ≤ p) (hdvd : component ∣ initialEquation center T)
    (inverse : Representative (localEquation N a g.polynomial))
    (hinverse : ConfluentSample.inverseAt? N g.polynomial
      (Geometry.projectPolynomial g.forward (initialSeparant center T)) a = some inverse) :
    ∃ P, prepare? p r k (SeriesNewton.scalarHom (localEquation N a g.polynomial)) center T
      (localInitialJet N g.polynomial a g.forward) inverse = some P := by
  apply prepare?_exists _ _ _ _ _ _ _ _ ⟨hrk, hkp⟩
  · rw [local_separant]
    exact (ConfluentSample.inverseAt?_sound N g.polynomial
      (Geometry.projectPolynomial g.forward (initialSeparant center T)) a inverse hinverse).1
  · exact local_initial_zero N component values g hg a center T hdvd

end ReedSolomon.HiddenDerivative.FastTaylor.TriangularPreparation
