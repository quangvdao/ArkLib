/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.Producer

/-! # Actual constructor points survive removal and supply the producer payload -/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ConstructorPoints

open CompPoly CPoly Polynomial TowerRepresentation PolynomialDifferential
open ReedSolomon.HiddenDerivative ReedSolomon.HiddenDerivative.FastTaylor

variable {E : Type} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E] {k : ℕ}

/-- A regular source solution gives nonvanishing of the stored chart separant at the inverse
projection point. This is derived from constructor geometry, not denominator substitution. -/
theorem constructor_point_separant (p Bjet : ℕ) [CharP E p] (values : List E)
    (source : ChartSource E 1) (entry : ChartEntry E 1 k)
    (hrun : constructSource? p 1 k Bjet values source = some entry)
    (P : E[X]) (hP : source.CoversSolution P) :
    let point := entry.point (polynomialJet source.center P)
    evalNested (chartPolynomials entry.chart).separant (RingHom.id E)
      (point 0) (point 1) ≠ 0 := by
  obtain ⟨_, _, hchart⟩ := constructSource?_sound p 1 k Bjet values source entry hrun
  obtain ⟨_, _, hforward, _, _, _, _, hsep⟩ := construct?_geometry p 1 k Bjet
    source.center source.equation source.component values entry.chart hchart
  let jet := polynomialJet (d := 1) source.center P
  let point := entry.point jet
  have hround : entry.chart.projection.mulVec point = jet :=
    Geometry.inverse_point_roundtrip entry.chart.projection entry.chart.inverseProjection
      hforward jet
  have hvalue : entry.chart.separant.eval point =
      MvPolynomial.aeval jet
        (initialJetSeparant source.center (semanticEquation source.equation)) := by
    rw [hsep, Geometry.eval_projectPolynomial, hround, CPoly.eval_equiv,
      initialSeparant_semantics]
    rfl
  have hnonzero : entry.chart.separant.eval point ≠ 0 := by
    rw [hvalue, aeval_initialJetSeparant]
    exact hP.2.2
  have hpoint : ![point 0, point 1] = point := by ext i; fin_cases i <;> rfl
  dsimp only
  rw [chartPolynomials, FirstOrderNormProducer.ChartPolynomials.ofChart,
    FirstOrderNormProducer.evalNested_bivariatePolynomial]
  change CMvPolynomial.eval₂ (RingHom.id E) ![point 0, point 1] entry.chart.separant ≠ 0
  rw [hpoint]
  simpa [CMvPolynomial.eval] using hnonzero

/-- The only remaining detector obligation for an actual regular constructor solution is
vanishing of the executed threshold at its free coordinate. The retained curve equation,
open-locus condition, and centered coefficient payload follow here. -/
theorem detected_of_constructor_threshold (p Bjet : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (values : List E)
    (source : ChartSource E 1) (entry : ChartEntry E 1 k)
    (hrun : constructSource? p 1 k Bjet values source = some entry)
    (hh : (chartPolynomials entry.chart).equation.monic)
    (hv : 0 < (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (A : ℕ) (gs : List (CPolynomial (CPolynomial E))) (out : FilterCore.Trace E)
    (hout : FilterCore.run p inverse A k (Producer.retained entry.chart) gs = some out)
    (P : E[X]) (hP : source.CoversSolution P)
    (hthreshold : out.thresholdPolynomial.toPoly.eval₂ (RingHom.id E)
      (entry.point (polynomialJet source.center P) 0) = 0) :
    Producer.Internal.WantedPointDetected p inverse entry.chart A gs P := by
  let point := entry.point (polynomialJet source.center P)
  have hs := constructor_point_separant p Bjet values source entry hrun P hP
  have heq := (entry.covers_solution values source hrun hv hB P hP).1
  have hpoint : ![point 0, point 1] = point := by ext i; fin_cases i <;> rfl
  have heqNested : evalNested (chartPolynomials entry.chart).equation
      (RingHom.id E) (point 0) (point 1) = 0 := by
    rw [chartPolynomials, FirstOrderNormProducer.ChartPolynomials.ofChart,
      FirstOrderNormProducer.evalNested_bivariatePolynomial, hpoint]
    simpa [CMvPolynomial.eval] using heq
  have hopen := ComponentRemoval.open_point_iff (RingHom.id E) (point 0) (point 1)
    (chartPolynomials entry.chart).equation (chartPolynomials entry.chart).separant
    (chartPolynomials entry.chart).equation.natDegree hh
  simp only [FirstOrderNormProducer.componentEvalAt_eq_evalNested] at hopen
  have hretained := (hopen hs).mpr heqNested
  exact ⟨out, point 0, point 1, hout, hthreshold, hretained, hs,
    CenteredCoverage.constructor_taylor_coefficients p Bjet values source entry hrun hv hB P hP⟩

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ConstructorPoints
