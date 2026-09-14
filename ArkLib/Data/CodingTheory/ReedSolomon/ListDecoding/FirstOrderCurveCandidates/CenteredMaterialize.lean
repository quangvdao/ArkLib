/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.DenominatorUnits
public import ArkLib.Data.Polynomial.CenteredCoefficients

/-! # Materialization with the chart's centered coefficient convention -/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.CenteredMaterialize

open CompPoly Polynomial Polynomial.CoefficientList TowerRepresentation TowerAlgebra
open ReedSolomon.HiddenDerivative.FastTaylor

variable {E : Type} [Field E] [BEq E] [LawfulBEq E] [DecidableEq E] {k width : ℕ}

/-- Change the coefficient basis inside the full tower algebra and restore canonical residues. -/
def recenter (center : E) (r : TowerRepresentation (F := E)) : TowerRepresentation (F := E) :=
  { r with coefficients := ((centeredToDescending
      (CPolynomial.C (CPolynomial.C center)) r.coefficients).map
        (reduceElement r.modulus r.fiber)) }

omit [DecidableEq E] in
theorem recenter_wellFormed (center : E) (r : TowerRepresentation (F := E))
    (hr : r.NonreducedWellFormed k) : (recenter center r).NonreducedWellFormed k := by
  refine ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
    hr.2.2.2.2.2.1, ?_, ?_⟩
  · simpa [recenter] using hr.2.2.2.2.2.2.1
  · intro c hc
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
    exact elementReduced_reduceElement hr.1 hr.2.2.2.1 hr.2.2.2.2.1 _

/-- Nested point evaluation as a ring homomorphism; it retains nonreduced source arithmetic. -/
noncomputable def evaluation {L : Type} [Field L] (ι : E →+* L) (u v : L) :
    CPolynomial (CPolynomial E) →+* L :=
  (Polynomial.evalRingHom v).comp
    ((Polynomial.mapRingHom (FirstOrderNormDecoder.D5.coefficientEval ι u)).comp
      CPolynomial.toPolyRingHom)

omit [DecidableEq E] in
theorem evaluation_apply {L : Type} [Field L] (ι : E →+* L) (u v : L)
    (a : CPolynomial (CPolynomial E)) :
    evaluation ι u v a = evalNested a ι u v := by
  simp [evaluation, evalNested, FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
    CPolynomial.toPolyRingHom_apply]

omit [DecidableEq E] in
@[simp] theorem evaluation_constant {L : Type} [Field L] (ι : E →+* L) (u v : L)
    (a : E) : evaluation ι u v (CPolynomial.C (CPolynomial.C a)) = ι a := by
  simp [evaluation, FirstOrderNormDecoder.D5.coefficientEval,
    CPolynomial.toPolyRingHom_apply, CPolynomial.toPoly_C]

omit [DecidableEq E] in
/-- Specialization of the executed change of basis is the inverse Taylor translation. -/
theorem recenter_specialize (center : E) (r : TowerRepresentation (F := E))
    (hr : r.NonreducedWellFormed k) {L : Type} [Field L]
    (ι : E →+* L) (u v : L) (hp : r.Point ι u v) :
    (recenter center r).specialize ι u v =
      taylor (-(ι center)) (ascendingPolynomial
        (r.coefficients.map fun c => evalNested c ι u v)) := by
  change JetHornerMachine.coefficientPolynomial
    (((centeredToDescending (CPolynomial.C (CPolynomial.C center)) r.coefficients).map
      (reduceElement r.modulus r.fiber)).map (fun c => evalNested c ι u v)) = _
  rw [List.map_map]
  have hm : (fun c => evalNested (reduceElement r.modulus r.fiber c) ι u v) =
      evaluation ι u v := by
    funext c
    rw [evaluation_apply]
    exact evalNested_reduceElement ι u v hr.1 hp.1 hr.2.2.2.1 hp.2 c
  change JetHornerMachine.coefficientPolynomial
    ((centeredToDescending (CPolynomial.C (CPolynomial.C center)) r.coefficients).map
      (fun c => evalNested (reduceElement r.modulus r.fiber c) ι u v)) = _
  rw [hm, map_centeredToDescending, evaluation_constant, centeredToDescending_polynomial]
  congr 2
  apply List.map_congr_left
  intro c _
  exact evaluation_apply ι u v c

/-- Materialize the actual denominator, then translate the ascending centered payload. -/
def run (chart : ChartData E 1 k) (r : TowerRepresentation (F := E)) :
    Option (TowerRepresentation (F := E)) :=
  (MaterializeChart.run chart r).map (recenter chart.center)

theorem run_exists (chart : ChartData E 1 k) (hregular : DenominatorRegular chart)
    (r : TowerRepresentation (F := E)) (hr : r.NonreducedWellFormed width)
    (hopen : DenominatorUnits.OnOpenChart chart r) : ∃ out, run chart r = some out := by
  obtain ⟨out, ho, _⟩ := DenominatorUnits.materialize_exists chart hregular r hr hopen
  exact ⟨recenter chart.center out, by simp [run, ho]⟩

theorem run_shape (chart : ChartData E 1 k) (r out : TowerRepresentation (F := E))
    (hr : r.NonreducedWellFormed width) (hout : run chart r = some out) :
    out.modulus = r.modulus ∧ out.fiber = r.fiber ∧ out.NonreducedWellFormed k := by
  obtain ⟨raw, hraw, rfl⟩ := Option.map_eq_some_iff.mp hout
  obtain ⟨hm, hf, hw⟩ := MaterializeChart.run_shape chart r raw hr hraw
  exact ⟨hm, hf, recenter_wellFormed chart.center raw hw⟩

/-- The actual materialized payload represents the original message whenever the stored
numerator ratios are its centered Taylor coefficients. -/
theorem run_specialize_of_taylor (chart : ChartData E 1 k)
    (r out : TowerRepresentation (F := E)) (hr : r.NonreducedWellFormed width)
    (hout : run chart r = some out) {L : Type} [Field L]
    (ι : E →+* L) (u v : L) (hp : r.Point ι u v) (p : L[X]) (hd : p.degree < k)
    (hcoeff : ∀ j : Fin k,
      evalNested ((chartPolynomials chart).numerators j) ι u v /
        evalNested (chartPolynomials chart).denominator ι u v =
          (taylor (ι chart.center) p).coeff j) :
    out.specialize ι u v = p := by
  obtain ⟨raw, hraw, rfl⟩ := Option.map_eq_some_iff.mp hout
  obtain ⟨hm, hf, hw⟩ := MaterializeChart.run_shape chart r raw hr hraw
  have hpraw : raw.Point ι u v := by simpa only [Point, hm, hf] using hp
  rw [recenter_specialize chart.center raw hw ι u v hpraw,
    MaterializeChart.run_specialize_coefficients chart r raw hr hraw ι u v hp]
  have hc : ((List.ofFn (chartPolynomials chart).numerators).map fun numerator =>
      evalNested numerator ι u v / evalNested (chartPolynomials chart).denominator ι u v) =
      List.ofFn (fun j : Fin k => (taylor (ι chart.center) p).coeff j) := by
    rw [List.map_ofFn]
    congr 1
    funext j
    exact hcoeff j
  rw [hc]
  rw [ascendingPolynomial_ofFn k _ (by simpa using hd), taylor_taylor,
    neg_add_cancel, taylor_zero]

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.CenteredMaterialize
