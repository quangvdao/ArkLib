/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.CenteredCoverage

/-! # Centered recovery from a retained open-curve filter

The retained equation may differ from the chart equation. Its divisibility into the original
equation transports localized points to the original chart, where the stored denominator and
Taylor provenance apply. Global component removal and threshold coverage are separate inputs.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.PreparedCoverage

open CompPoly Polynomial TowerRepresentation TowerAlgebra PolynomialDifferential
open ReedSolomon.HiddenDerivative ReedSolomon.HiddenDerivative.FastTaylor

variable {E : Type} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E] {k : ℕ}

omit [DecidableEq E] in
/-- A retained equation factor sends every geometric point to the original equation. -/
theorem equation_zero_of_retained_dvd (chart : ChartData E 1 k)
    (h : CPolynomial (CPolynomial E)) (hdiv : h ∣ (chartPolynomials chart).equation)
    {L : Type} [Field L] (ι : E →+* L) (u v : L) (hz : evalNested h ι u v = 0) :
    evalNested (chartPolynomials chart).equation ι u v = 0 := by
  obtain ⟨q, hq⟩ := hdiv
  rw [hq, evalNested_mul, hz, zero_mul]

/-- The executed finite family of centered message components from an arbitrary retained
equation and the actual chart separant. -/
def fromFilter (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (A : ℕ) (h : CPolynomial (CPolynomial E))
    (gs : List (CPolynomial (CPolynomial E))) (out : FilterCore.Trace E)
    (hout : FilterCore.run p inverse A k h gs = some out)
    (G : CPolynomial E) (hG : out.base = some G) (hGpos : 0 < G.natDegree)
    (hh : h.monic) (hhpos : 0 < (reduceBase G h).natDegree) :
    List (AgreementRecovery.Tower.Component E k) :=
  CenteredCoverage.components chart
    (TowerCore.fromFilter p inverse hinverse A k h gs out hout G hG hGpos hh hhpos
      (chartPolynomials chart).separant).towers
    (TowerCore.fromFilter_wellFormed p inverse hinverse A k h gs out hout G hG hGpos hh hhpos
      (chartPolynomials chart).separant)

omit [DecidableEq E] in
/-- Retained-factor localization satisfies the original chart's open-locus contract. -/
theorem fromFilter_onOpenChart (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (A : ℕ) (h : CPolynomial (CPolynomial E))
    (hdiv : h ∣ (chartPolynomials chart).equation)
    (gs : List (CPolynomial (CPolynomial E))) (out : FilterCore.Trace E)
    (hout : FilterCore.run p inverse A k h gs = some out)
    (G : CPolynomial E) (hG : out.base = some G) (hGpos : 0 < G.natDegree)
    (hh : h.monic) (hhpos : 0 < (reduceBase G h).natDegree)
    (r : TowerRepresentation (F := E))
    (hr : r ∈ (TowerCore.fromFilter p inverse hinverse A k h gs out hout G hG hGpos hh hhpos
      (chartPolynomials chart).separant).towers) : DenominatorUnits.OnOpenChart chart r := by
  intro u v hp
  have hs := (TowerCore.fromFilter_point_iff p inverse hinverse A k h gs out hout G hG
    hGpos hh hhpos (chartPolynomials chart).separant
    (algebraMap E (AlgebraicClosure E)) u v).mp ⟨r, hr, hp⟩
  exact ⟨equation_zero_of_retained_dvd chart h hdiv _ u v hs.1.2, hs.2⟩

/-- Local coverage for a prepared curve: a threshold root on the retained open curve gives
an actual represented component. The coefficient identity is derived from the executed Taylor
constructor, with both coefficient order and its original center accounted for. -/
theorem representedBy_of_constructor_threshold (p Bjet : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a) (values : List E)
    (source : ChartSource E 1) (entry : ChartEntry E 1 k)
    (hrun : constructSource? p 1 k Bjet values source = some entry)
    (hv : 0 < (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (hregular : DenominatorRegular entry.chart)
    (A : ℕ) (h : CPolynomial (CPolynomial E))
    (hdiv : h ∣ (chartPolynomials entry.chart).equation)
    (gs : List (CPolynomial (CPolynomial E))) (out : FilterCore.Trace E)
    (hout : FilterCore.run p inverse A k h gs = some out)
    (G : CPolynomial E) (hG : out.base = some G) (hGpos : 0 < G.natDegree)
    (hh : h.monic) (hhpos : 0 < (reduceBase G h).natDegree)
    (P : E[X]) (hd : P.degree < k) (hP : source.CoversSolution P)
    (hpoint : let point := entry.point (polynomialJet source.center P)
      (out.thresholdPolynomial.toPoly.eval₂ (RingHom.id E) (point 0) = 0 ∧
        evalNested h (RingHom.id E) (point 0) (point 1) = 0) ∧
          evalNested (chartPolynomials entry.chart).separant
            (RingHom.id E) (point 0) (point 1) ≠ 0) :
    AgreementRecovery.Tower.RepresentedBy (RingHom.id E) (RingHom.id E) k
      (fromFilter p inverse hinverse entry.chart A h gs out hout G hG hGpos hh hhpos) P := by
  let point := entry.point (polynomialJet source.center P)
  obtain ⟨r, hr, hp⟩ := (TowerCore.fromFilter_point_iff p inverse hinverse A k h gs out hout G hG
    hGpos hh hhpos (chartPolynomials entry.chart).separant
    (RingHom.id E) (point 0) (point 1)).mpr hpoint
  exact CenteredCoverage.representedBy_of_constructor_point p Bjet values source entry hrun
    hv hB hregular _
    (TowerCore.fromFilter_wellFormed p inverse hinverse A k h gs out hout G hG hGpos hh hhpos
      (chartPolynomials entry.chart).separant)
    (fromFilter_onOpenChart p inverse hinverse entry.chart A h hdiv gs out hout G hG
      hGpos hh hhpos) P hd hP r hr hp

/-- Centered materialization only changes coefficient slots; discarded failed inversions can
only decrease the total dimension of the represented parameter algebras. -/
theorem components_dimension_le (chart : ChartData E 1 k)
    (rs : List (TowerRepresentation (F := E))) {width : ℕ}
    (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width) :
    ((CenteredCoverage.components chart rs hrs).map fun c => c.val.dimension).sum ≤
      (rs.map TowerRepresentation.dimension).sum := by
  have hraw : ((RecoveryComponents.materializeComponents chart rs hrs).map
      fun c => c.val.dimension).sum ≤ (rs.map TowerRepresentation.dimension).sum := by
    induction rs with
    | nil => simp [RecoveryComponents.materializeComponents]
    | cons r rs ih =>
      simp only [RecoveryComponents.materializeComponents]
      split
      · simpa only [List.map_cons, List.sum_cons] using
          (ih (fun a ha => hrs a (List.mem_cons_of_mem _ ha))).trans
            (Nat.le_add_left _ r.dimension)
      · rename_i raw hraw
        have hs := MaterializeChart.run_shape chart r raw (hrs r List.mem_cons_self) hraw
        simpa only [List.map_cons, List.sum_cons, dimension, hs.1, hs.2.1] using
          Nat.add_le_add_left (ih (fun a ha => hrs a (List.mem_cons_of_mem _ ha))) r.dimension
  unfold CenteredCoverage.components
  rw [List.map_map]
  exact hraw

/-- The prepared centered family's dimension is bounded by the original parameter tower. -/
theorem fromFilter_dimension_le (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (A : ℕ) (h : CPolynomial (CPolynomial E))
    (gs : List (CPolynomial (CPolynomial E))) (out : FilterCore.Trace E)
    (hout : FilterCore.run p inverse A k h gs = some out)
    (G : CPolynomial E) (hG : out.base = some G) (hGpos : 0 < G.natDegree)
    (hh : h.monic) (hhpos : 0 < (reduceBase G h).natDegree) :
    ((fromFilter p inverse hinverse chart A h gs out hout G hG hGpos hh hhpos).map
      fun c => c.val.dimension).sum ≤ G.natDegree * h.natDegree := by
  have hbound : ((fromFilter p inverse hinverse chart A h gs out hout G hG hGpos hh hhpos).map
      fun c => c.val.dimension).sum ≤ (TowerCore.parameterTower G h).dimension := by
    apply (components_dimension_le chart _ _).trans
    exact localizeFiber_dimension_le _ _ _
  have hGmonic := (FilterCore.run_base_squarefree_monic p inverse hinverse A k h gs
    out hout G hG).2
  simpa only [dimension, TowerCore.parameterTower, natDegree_reduceBase G hGmonic hGpos h hh]
    using hbound

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.PreparedCoverage
