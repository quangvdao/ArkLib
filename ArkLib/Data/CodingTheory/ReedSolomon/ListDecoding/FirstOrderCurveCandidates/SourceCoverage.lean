/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ConstructorPoints
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ComponentAgreementBound
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ThresholdCoverage
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.ConstructorSquarefree

/-! # Actual-source completeness of the executable curve producer -/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.SourceCoverage

open CompPoly CPoly Polynomial TowerRepresentation PolynomialDifferential
open Polynomial.FunctionFieldAlgorithms
open ReedSolomon.HiddenDerivative ReedSolomon.HiddenDerivative.FastTaylor

variable {E : Type} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E] {k n : ℕ}

omit [DecidableEq E] [BEq E] [LawfulBEq E] in
private theorem taylor_sum_eval (P : E[X]) (center alpha : E) (hk : 0 < k)
    (hd : P.degree < k) :
    (∑ j : Fin k, (taylor center P).coeff j * (alpha - center) ^ j.val) = P.eval alpha := by
  have hnat : (taylor center P).natDegree < k := by
    rw [natDegree_taylor]
    by_cases hp : P = 0
    · simpa [hp] using hk
    · exact (natDegree_lt_iff_degree_lt hp).mpr hd
  rw [Fin.sum_univ_eq_sum_range (fun j => (taylor center P).coeff j * (alpha - center) ^ j),
    ← Polynomial.eval_eq_sum_range' hnat, taylor_eval]
  simp

/-- An agreeing received position kills its actual stored residual at the source solution's
inverse-projection point. Centered coefficients are interpreted at the original center. -/
theorem agreement_zero_of_source (p Bjet : ℕ) [CharP E p] (values : List E)
    (source : ChartSource E 1) (entry : ChartEntry E 1 k)
    (hrun : constructSource? p 1 k Bjet values source = some entry)
    (hv : 0 < (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (P : E[X]) (hd : P.degree < k) (hP : source.CoversSolution P)
    (alpha received : E) (hag : P.eval alpha = received) :
    let point := entry.point (polynomialJet source.center P)
    ComponentDescent.evalAt (RingHom.id E) (point 0) (point 1)
      (agreementPolynomial entry.chart alpha received) = 0 := by
  obtain ⟨_, _, hchart⟩ := constructSource?_sound p 1 k Bjet values source entry hrun
  have hgeo := construct?_geometry p 1 k Bjet source.center source.equation
    source.component values entry.chart hchart
  obtain ⟨_, hden, hcoeff⟩ := entry.covers_solution values source hrun hv hB P hP
  let point := entry.point (polynomialJet source.center P)
  have hpoint : ![point 0, point 1] = point := by ext i; fin_cases i <;> rfl
  have hclear (j : Fin k) : CMvPolynomial.eval₂ (RingHom.id E) point
      (entry.chart.numerators j) = CMvPolynomial.eval₂ (RingHom.id E) point
        entry.chart.denominator * (taylor source.center P).coeff j := by
    have hc := (div_eq_iff hden).mp (hcoeff j)
    simpa [ChartData.coefficientAt, CMvPolynomial.eval, mul_comm] using hc
  dsimp only
  rw [FirstOrderNormProducer.componentEvalAt_eq_evalNested, agreementPolynomial,
    FirstOrderNormProducer.ChartPolynomials.agreement,
    FirstOrderNormProducer.evalNested_bivariatePolynomial, hpoint,
    entry.chart.eval₂_agreement_of_cleared (RingHom.id E) point
      (fun j : Fin k => (taylor source.center P).coeff j) hclear]
  simp only [RingHom.id_apply, hgeo.2.1]
  rw [taylor_sum_eval P source.center alpha (by omega) hd, hag, sub_self, mul_zero]

/-- All geometric and coefficient detector obligations follow from the actual source run,
its regular polynomial solution, and the received agreement count. -/
theorem detected_of_source (p Bjet : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (values : List E)
    (source : ChartSource E 1) (entry : ChartEntry E 1 k)
    (hrun : constructSource? p 1 k Bjet values source = some entry)
    (hv : 0 < (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (hcomponent : Squarefree
      (CBivariate.toPoly (BivariateReducedSupport.fromOrdinaryCMv source.component)))
    (A : ℕ) (hAk : k ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ E) (received : Fin n → E)
    (P : E[X]) (hd : P.degree < k) (hP : source.CoversSolution P)
    (hag : A ≤ Code.agree (evalOnPoints domain P) received) :
    Producer.WantedPointDetected p inverse entry.chart A
      (Producer.agreementRows entry.chart domain received) P := by
  classical
  obtain ⟨_, _, hchart⟩ := constructSource?_sound p 1 k Bjet values source entry hrun
  have hgeo := construct?_geometry p 1 k Bjet source.center source.equation
    source.component values entry.chart hchart
  have hk : 0 < k := by omega
  have hh := equation_monic_of_normalForms entry.chart
    (construct?_normalForms p 1 k Bjet source.center source.equation
      source.component values hv hB entry.chart hchart)
  let h := Producer.retained entry.chart
  let gs := Producer.agreementRows entry.chart domain received
  have hm : h.monic := Producer.retained_monic entry.chart hh
  have hsorig := FirstOrderNormProducer.construct?_genericSquarefree p Bjet source.center
    source.equation source.component values hv hB entry.chart hchart hcomponent
  have hs : Squarefree (ClearDenominators.valueGlobal h) := by
    apply Squarefree.squarefree_of_dvd _ hsorig
    obtain ⟨q, hq⟩ := Producer.retained_dvd entry.chart hh
    refine ⟨ClearDenominators.valueGlobal q, ?_⟩
    rw [← ClearDenominators.valueGlobal_mul]
    exact congrArg ClearDenominators.valueGlobal hq
  let point := entry.point (polynomialJet source.center P)
  have hsep := ConstructorPoints.constructor_point_separant p Bjet values source entry hrun P hP
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
  have hp : ComponentDescent.evalAt (RingHom.id E) (point 0) (point 1) h = 0 := by
    rw [FirstOrderNormProducer.componentEvalAt_eq_evalNested]
    exact (hopen hsep).mpr heqNested
  have hlen : gs.length = n := by simp [gs, Producer.agreementRows]
  obtain ⟨out, hout⟩ := FilterCore.run_exists p inverse A k h gs hk hAk (by omega)
  apply ConstructorPoints.detected_of_constructor_threshold p Bjet inverse values source entry
    hrun hh hv hB A gs out hout P hP
  have ht := ThresholdCoverage.run_threshold_vanishes_fin (RingHom.id E) (point 0) (point 1)
    p inverse A k h gs hm hs hp hk hAk (by omega)
  let e : Fin gs.length ≃ Fin n := finCongr hlen
  let S : Finset (Fin n) := Finset.univ.filter fun i => P.eval (domain i) = received i
  apply ht (S.map e.symm.toEmbedding) ?_ ?_ ?_ out hout
  · rw [Finset.card_map]
    have heq : S = (Finset.univ.filter fun i => evalOnPoints domain P i = received i) := by
      ext i
      change (i ∈ Finset.univ.filter (fun j => P.eval (domain j) = received j)) ↔ _
      rw [Finset.mem_filter, Finset.mem_filter]
      rfl
    rw [heq]
    exact hag
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    have he := agreement_zero_of_source p Bjet values source entry hrun hv hB P hd hP
      (domain j) (received j) (Finset.mem_filter.mp hj).2
    have hiVal : (e.symm.toEmbedding j).val = j.val := rfl
    have hlookup : gs[j.val]? = some (agreementPolynomial entry.chart (domain j) (received j)) := by
      simp [gs, Producer.agreementRows]
    have hx : gs[(e.symm.toEmbedding j).val]? =
        some (agreementPolynomial entry.chart (domain j) (received j)) := by
      rw [hiVal]
      exact hlookup
    rw [List.getElem?_eq_getElem (e.symm.toEmbedding j).isLt] at hx
    have hrow := Option.some.inj hx
    change ComponentDescent.evalAt (RingHom.id E) (point 0) (point 1)
      gs[(e.symm.toEmbedding j).val] = 0
    rw [hrow]
    exact he
  · intro block hblock hzero
    apply ComponentAgreementBound.retained_block_universal_length_le_pred p Bjet source.center
      source.equation source.component values hv hB entry.chart hchart domain received block hblock
    exact ComponentAgreementBound.positive_degree_of_point (RingHom.id E) (point 0) (point 1)
      block.modulus (ComponentDescent.run_monic h gs hm block hblock) hzero

/-- Exact output for the executed chart-local decoder from actual source solution coverage.
No threshold-root, represented-component, or rational-payload identity is assumed. -/
theorem decode_exact_of_source_coverage (p Bjet : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a) (values : List E)
    (source : ChartSource E 1) (entry : ChartEntry E 1 k)
    (hrun : constructSource? p 1 k Bjet values source = some entry)
    (hv : 0 < (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (hcomponent : Squarefree
      (CBivariate.toPoly (BivariateReducedSupport.fromOrdinaryCMv source.component)))
    (hh : (chartPolynomials entry.chart).equation.monic)
    (hregular : DenominatorRegular entry.chart)
    (A : ℕ) (hAk : k ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ E) (received : Fin n → E)
    (hcover : ∀ P : E[X], P.degree < k → A ≤ Code.agree (evalOnPoints domain P) received →
      source.CoversSolution P) :
    ExactOutput domain received k A
      (Producer.decode p inverse hinverse entry.chart hh A domain received) := by
  apply Producer.decode_exact p inverse hinverse entry.chart hh hregular A hAk domain received
  intro P hd ha
  exact detected_of_source p Bjet inverse values source entry hrun hv hB hcomponent
    A hAk hAn domain received P hd (hcover P hd ha) ha

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.SourceCoverage
