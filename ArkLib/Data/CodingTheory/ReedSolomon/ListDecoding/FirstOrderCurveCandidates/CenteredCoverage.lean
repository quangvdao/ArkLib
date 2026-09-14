/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.CenteredMaterialize
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.Coverage
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Coverage
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.ComponentNorms

/-! # Recovery of the original message from actual Taylor-constructor provenance

The finite component producer must still expose the source point. Once it does, the executed
materialization and change of basis recover the original polynomial, including nonzero centers.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.CenteredCoverage

open CompPoly Polynomial TowerRepresentation
open ReedSolomon.HiddenDerivative ReedSolomon.HiddenDerivative.FastTaylor
open PolynomialDifferential

variable {E : Type} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E] {k width n : ℕ}

/-- The actual finite family, with centered ascending payloads converted for recovery. -/
def components (chart : ChartData E 1 k) (rs : List (TowerRepresentation (F := E)))
    (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width) :
    List (AgreementRecovery.Tower.Component E k) :=
  (RecoveryComponents.materializeComponents chart rs hrs).map fun c =>
    ⟨CenteredMaterialize.recenter chart.center c.val,
      CenteredMaterialize.recenter_wellFormed chart.center c.val c.property⟩

/-- Every actual materialized chart point with the correct Taylor coefficients is represented
in the executed centered family. -/
theorem representedBy_of_taylor_point (chart : ChartData E 1 k)
    (rs : List (TowerRepresentation (F := E))) (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width)
    (r raw : TowerRepresentation (F := E)) (hr : r ∈ rs)
    (hraw : MaterializeChart.run chart r = some raw) (u v : E)
    (hp : r.Point (RingHom.id E) u v) (P : E[X]) (hd : P.degree < k)
    (hc : ∀ j : Fin k, evalNested ((chartPolynomials chart).numerators j) (RingHom.id E) u v /
      evalNested (chartPolynomials chart).denominator (RingHom.id E) u v =
        (taylor chart.center P).coeff j) :
    AgreementRecovery.Tower.RepresentedBy (RingHom.id E) (RingHom.id E) k
      (components chart rs hrs) P := by
  let c : AgreementRecovery.Tower.Component E k :=
    ⟨raw, (MaterializeChart.run_shape chart r raw (hrs r hr) hraw).2.2⟩
  let out : AgreementRecovery.Tower.Component E k :=
    ⟨CenteredMaterialize.recenter chart.center raw,
      CenteredMaterialize.recenter_wellFormed chart.center raw c.property⟩
  have ho : CenteredMaterialize.run chart r = some out.val := by
    simp [CenteredMaterialize.run, hraw, out]
  refine ⟨out, List.mem_map.mpr ⟨c, ?_, rfl⟩, u, v, ?_, ?_⟩
  · exact (RecoveryComponents.mem_materializeComponents_iff chart rs hrs c).mpr
      ⟨r, hr, hraw⟩
  · obtain ⟨hm, hf, _⟩ := CenteredMaterialize.run_shape chart r out.val (hrs r hr) ho
    simpa only [Point, hm, hf] using hp
  · simpa using CenteredMaterialize.run_specialize_of_taylor chart r out.val
      (hrs r hr) ho (RingHom.id E) u v hp P hd hc

/-- The source constructor discharges the coefficient identity from its literal numerator
contract and differential-solution semantics. -/
theorem constructor_taylor_coefficients (p Bjet : ℕ) [CharP E p] (values : List E)
    (source : ChartSource E 1) (entry : ChartEntry E 1 k)
    (hrun : constructSource? p 1 k Bjet values source = some entry)
    (hv : 0 < (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (P : E[X]) (hP : source.CoversSolution P) (j : Fin k) :
    let point := entry.point (polynomialJet source.center P)
    evalNested ((chartPolynomials entry.chart).numerators j) (RingHom.id E) (point 0) (point 1) /
      evalNested (chartPolynomials entry.chart).denominator (RingHom.id E) (point 0) (point 1) =
        (taylor entry.chart.center P).coeff j := by
  obtain ⟨_, _, hchart⟩ := constructSource?_sound p 1 k Bjet values source entry hrun
  have hcenter := (construct?_geometry p 1 k Bjet source.center source.equation
    source.component values entry.chart hchart).2.1
  have hc := (entry.covers_solution values source hrun hv hB P hP).2.2 j
  let point := entry.point (polynomialJet source.center P)
  have hpoint : ![point 0, point 1] = point := by ext i; fin_cases i <;> rfl
  dsimp only
  rw [chartPolynomials, FirstOrderNormProducer.ChartPolynomials.ofChart,
    FirstOrderNormProducer.evalNested_bivariatePolynomial,
    FirstOrderNormProducer.evalNested_bivariatePolynomial, hcenter]
  change CPoly.CMvPolynomial.eval₂ (RingHom.id E) ![point 0, point 1] _ /
    CPoly.CMvPolynomial.eval₂ (RingHom.id E) ![point 0, point 1] _ = _
  rw [hpoint]
  simpa [ChartData.coefficientAt, CPoly.CMvPolynomial.eval] using hc

/-- A successful source constructor and an actual source-tower point suffice for representation;
the polynomial payload identity is discharged by constructor provenance. -/
theorem representedBy_of_constructor_point (p Bjet : ℕ) [CharP E p] (values : List E)
    (source : ChartSource E 1) (entry : ChartEntry E 1 k)
    (hrun : constructSource? p 1 k Bjet values source = some entry)
    (hv : 0 < (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (hregular : DenominatorRegular entry.chart)
    (rs : List (TowerRepresentation (F := E))) (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width)
    (hopen : ∀ r ∈ rs, DenominatorUnits.OnOpenChart entry.chart r)
    (P : E[X]) (hd : P.degree < k) (hP : source.CoversSolution P)
    (r : TowerRepresentation (F := E)) (hr : r ∈ rs)
    (hp : let point := entry.point (polynomialJet source.center P)
      r.Point (RingHom.id E) (point 0) (point 1)) :
    AgreementRecovery.Tower.RepresentedBy (RingHom.id E) (RingHom.id E) k
      (components entry.chart rs hrs) P := by
  obtain ⟨raw, hraw, _⟩ := DenominatorUnits.materialize_exists entry.chart hregular r
    (hrs r hr) (hopen r hr)
  exact representedBy_of_taylor_point entry.chart rs hrs r raw hr hraw _ _ hp P hd
    (constructor_taylor_coefficients p Bjet values source entry hrun hv hB P hP)

/-- Checked recovery on the centered family. -/
def recover (chart : ChartData E 1 k) (rs : List (TowerRepresentation (F := E)))
    (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width)
    (domain : Fin n ↪ E) (received : Fin n → E) (A : ℕ) : List (List E) :=
  AgreementRecovery.Tower.recoverAgreement (RingHom.id E) domain received k A
    (components chart rs hrs)

/-- Exact recovery follows from actual source-tower points and centered coefficients.
`constructor_taylor_coefficients` supplies the coefficient clause for successful source runs. -/
theorem recover_exact_of_taylor_coverage (chart : ChartData E 1 k)
    (hregular : DenominatorRegular chart)
    (rs : List (TowerRepresentation (F := E))) (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width)
    (hopen : ∀ r ∈ rs, DenominatorUnits.OnOpenChart chart r)
    (domain : Fin n ↪ E) (received : Fin n → E) (A : ℕ) (hAk : k ≤ A)
    (hcover : ∀ P : E[X], P.degree < k → A ≤ Code.agree (evalOnPoints domain P) received →
      ∃ r ∈ rs, ∃ u v, r.Point (RingHom.id E) u v ∧
        ∀ j : Fin k,
          evalNested ((chartPolynomials chart).numerators j) (RingHom.id E) u v /
            evalNested (chartPolynomials chart).denominator (RingHom.id E) u v =
              (taylor chart.center P).coeff j) :
    ExactOutput domain received k A (recover chart rs hrs domain received A) := by
  apply AgreementRecovery.Tower.recoverAgreement_exact_of_coverage
    (RingHom.id E) (RingHom.id E) domain received k A hAk
  intro P hd ha
  obtain ⟨r, hr, u, v, hp, hc⟩ := hcover P hd ha
  obtain ⟨raw, hraw, _⟩ := DenominatorUnits.materialize_exists chart hregular r
    (hrs r hr) (hopen r hr)
  exact representedBy_of_taylor_point chart rs hrs r raw hr hraw u v hp P hd hc

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.CenteredCoverage
