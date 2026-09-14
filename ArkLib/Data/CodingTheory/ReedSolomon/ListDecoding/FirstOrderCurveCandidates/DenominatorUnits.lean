/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.MaterializeChart
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.TowerCore
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.NonreducedUnits

/-!
# Actual chart denominator units after localization

Denominator regularity is used only at geometric points on the chart equation where the
separant is nonzero. Weak-tower geometric unitness then supplies an inverse of the actual stored
denominator, even when the retained fibers contain nilpotents. No equality between the stored
denominator and a separant power, and no candidate-coverage premise, is used.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.DenominatorUnits

open CompPoly TowerRepresentation TowerAlgebra
open ReedSolomon.HiddenDerivative.FastTaylor

variable {E : Type} [Field E] [BEq E] [LawfulBEq E] {k : ℕ}

/-- The sole geometric interface needed by denominator regularity. -/
def OnOpenChart (chart : ChartData E 1 k) (r : TowerRepresentation (F := E)) : Prop :=
  ∀ x y : AlgebraicClosure E, r.Point (algebraMap E (AlgebraicClosure E)) x y →
    evalNested (chartPolynomials chart).equation (algebraMap E (AlgebraicClosure E)) x y = 0 ∧
      evalNested (chartPolynomials chart).separant (algebraMap E (AlgebraicClosure E)) x y ≠ 0

/-- Regularity makes the actual denominator a unit in every weak tower on the open chart. -/
theorem denominator_isTowerUnit (chart : ChartData E 1 k) (hregular : DenominatorRegular chart)
    (r : TowerRepresentation (F := E)) {width : ℕ} (hr : r.NonreducedWellFormed width)
    (hopen : OnOpenChart chart r) :
    IsTowerUnit r.modulus r.fiber (chartPolynomials chart).denominator := by
  apply isTowerUnit_of_geometric_nonvanishing_nonreduced r hr
  intro x y hp
  exact hregular x y (hopen x y hp).1 (hopen x y hp).2

/-- Localizing a tower on the chart equation at the separant supplies the open-chart interface. -/
theorem localize_onOpenChart (chart : ChartData E 1 k)
    (r : TowerRepresentation (F := E)) {width : ℕ} (hr : r.NonreducedWellFormed width)
    (hcurve : ∀ x y : AlgebraicClosure E,
      r.Point (algebraMap E (AlgebraicClosure E)) x y →
        evalNested (chartPolynomials chart).equation (algebraMap E (AlgebraicClosure E)) x y = 0)
    (child : TowerRepresentation (F := E))
    (hc : child ∈ localizeFiber r (chartPolynomials chart).separant hr) :
    OnOpenChart chart child := by
  intro x y hp
  have hparent := (localizeFiber_point_iff r (chartPolynomials chart).separant hr
    (algebraMap E (AlgebraicClosure E)) x y).mp ⟨child, hc, hp⟩
  exact ⟨hcurve x y hparent.1, hparent.2⟩

/-- Regularity now guarantees actual materialization, including all `k` coefficient slots. -/
theorem materialize_exists [DecidableEq E]
    (chart : ChartData E 1 k) (hregular : DenominatorRegular chart)
    (r : TowerRepresentation (F := E)) {width : ℕ} (hr : r.NonreducedWellFormed width)
    (hopen : OnOpenChart chart r) :
    ∃ out, MaterializeChart.run chart r = some out ∧
      out.modulus = r.modulus ∧ out.fiber = r.fiber ∧ out.NonreducedWellFormed k := by
  obtain ⟨out, ho⟩ := MaterializeChart.run_exists chart r hr
    (denominator_isTowerUnit chart hregular r hr hopen)
  exact ⟨out, ho, MaterializeChart.run_shape chart r out hr ho⟩

/-- Successful base-filter localization on the actual chart equation lies on its open chart. -/
theorem fromFilter_onOpenChart (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (A : ℕ)
    (gs : List (CPolynomial (CPolynomial E))) (out : FilterCore.Trace E)
    (hout : FilterCore.run p inverse A k (chartPolynomials chart).equation gs = some out)
    (G : CPolynomial E) (hG : out.base = some G) (hGpos : 0 < G.natDegree)
    (hh : (chartPolynomials chart).equation.monic)
    (hhpos : 0 < (reduceBase G (chartPolynomials chart).equation).natDegree)
    (child : TowerRepresentation (F := E))
    (hc : child ∈ (TowerCore.fromFilter p inverse hinverse A k
      (chartPolynomials chart).equation gs out hout G hG hGpos hh hhpos
      (chartPolynomials chart).separant).towers) : OnOpenChart chart child := by
  intro x y hp
  have hs := (TowerCore.fromFilter_point_iff p inverse hinverse A k
    (chartPolynomials chart).equation gs out hout G hG hGpos hh hhpos
    (chartPolynomials chart).separant (algebraMap E (AlgebraicClosure E)) x y).mp
      ⟨child, hc, hp⟩
  exact ⟨hs.1.2, hs.2⟩

/-- Every actual localized filter child has a successful weak-tower chart materialization. -/
theorem fromFilter_materialize_exists [DecidableEq E]
    (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (hregular : DenominatorRegular chart) (A : ℕ)
    (gs : List (CPolynomial (CPolynomial E))) (out : FilterCore.Trace E)
    (hout : FilterCore.run p inverse A k (chartPolynomials chart).equation gs = some out)
    (G : CPolynomial E) (hG : out.base = some G) (hGpos : 0 < G.natDegree)
    (hh : (chartPolynomials chart).equation.monic)
    (hhpos : 0 < (reduceBase G (chartPolynomials chart).equation).natDegree)
    (child : TowerRepresentation (F := E))
    (hc : child ∈ (TowerCore.fromFilter p inverse hinverse A k
      (chartPolynomials chart).equation gs out hout G hG hGpos hh hhpos
      (chartPolynomials chart).separant).towers) :
    ∃ materialized, MaterializeChart.run chart child = some materialized ∧
      materialized.modulus = child.modulus ∧ materialized.fiber = child.fiber ∧
      materialized.NonreducedWellFormed k := by
  apply materialize_exists chart hregular child
  · exact TowerCore.fromFilter_wellFormed p inverse hinverse A k
      (chartPolynomials chart).equation gs out hout G hG hGpos hh hhpos
      (chartPolynomials chart).separant child hc
  · exact fromFilter_onOpenChart p inverse hinverse chart A gs out hout G hG
      hGpos hh hhpos child hc

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.DenominatorUnits
