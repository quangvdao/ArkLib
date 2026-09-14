/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.RecoveryComponents
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.TowerCorrectness

/-!
# Conditional recovery coverage from actual chart points

The coverage premise names an actual source tower, its geometric point, and the rational
specialization of the stored numerator list. Materialization and recovery are the executed
operations. No global coverage theorem or centered-Taylor/order conversion is asserted here;
the explicit rational polynomial identity remains the constructor's obligation.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.Coverage

open CompPoly Polynomial Polynomial.JetHornerMachine TowerRepresentation
open ReedSolomon.HiddenDerivative.FastTaylor

variable {F E L : Type} [Field F]
  [Field E] [DecidableEq E] [BEq E] [LawfulBEq E] [Field L] {k width n : ℕ}

/-- The exact rational polynomial in the stored list's descending Horner convention. -/
noncomputable def rationalPolynomial (chart : ChartData E 1 k) (ι : E →+* L) (u v : L) : L[X] :=
  coefficientPolynomial ((List.ofFn (chartPolynomials chart).numerators).map fun numerator =>
    evalNested numerator ι u v / evalNested (chartPolynomials chart).denominator ι u v)

/-- A source point with a successful actual materialization supplies a represented component. -/
theorem representedBy_of_materialized_point
    (chart : ChartData E 1 k) (rs : List (TowerRepresentation (F := E)))
    (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width) (base : F →+* E) (ι : E →+* L)
    (r out : TowerRepresentation (F := E)) (hr : r ∈ rs)
    (hout : MaterializeChart.run chart r = some out) (u v : L) (hp : r.Point ι u v)
    (p : F[X]) (hpoly : rationalPolynomial chart ι u v = p.map (ι.comp base)) :
    AgreementRecovery.Tower.RepresentedBy base ι k
      (RecoveryComponents.materializeComponents chart rs hrs) p := by
  have hs := MaterializeChart.run_shape chart r out (hrs r hr) hout
  let c : AgreementRecovery.Tower.Component E k := ⟨out, hs.2.2⟩
  refine ⟨c, (RecoveryComponents.mem_materializeComponents_iff chart rs hrs c).mpr
    ⟨r, hr, hout⟩, u, v, ?_, ?_⟩
  · change out.Point ι u v
    simpa only [Point, hs.1, hs.2.1] using hp
  · exact (MaterializeChart.run_specialize chart r out (hrs r hr) hout ι u v hp).trans hpoly

/-- Regularity discharges successful inversion; the rational message identity stays explicit. -/
theorem representedBy_of_regular_point
    (chart : ChartData E 1 k) (hregular : DenominatorRegular chart)
    (rs : List (TowerRepresentation (F := E))) (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width)
    (hopen : ∀ r ∈ rs, DenominatorUnits.OnOpenChart chart r)
    (base : F →+* E) (ι : E →+* L) (r : TowerRepresentation (F := E)) (hr : r ∈ rs)
    (u v : L) (hp : r.Point ι u v) (p : F[X])
    (hpoly : rationalPolynomial chart ι u v = p.map (ι.comp base)) :
    AgreementRecovery.Tower.RepresentedBy base ι k
      (RecoveryComponents.materializeComponents chart rs hrs) p := by
  obtain ⟨out, ho, _⟩ := DenominatorUnits.materialize_exists chart hregular r
    (hrs r hr) (hopen r hr)
  exact representedBy_of_materialized_point chart rs hrs base ι r out hr ho u v hp p hpoly

variable [DecidableEq F] [BEq F] [LawfulBEq F]

/-- Explicit materializable source coverage yields exact checked recovery, without a
`RepresentedBy` oracle in the premise. -/
theorem recover_exact_of_materializable_coverage
    (chart : ChartData E 1 k) (rs : List (TowerRepresentation (F := E)))
    (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width)
    (base : F →+* E) (ι : E →+* L) (domain : Fin n ↪ F) (received : Fin n → F)
    (A : ℕ) (hAk : k ≤ A)
    (hcover : ∀ p : F[X], p.degree < k → A ≤ Code.agree (evalOnPoints domain p) received →
      ∃ r ∈ rs, ∃ out u v, MaterializeChart.run chart r = some out ∧ r.Point ι u v ∧
        rationalPolynomial chart ι u v = p.map (ι.comp base)) :
    ExactOutput domain received k A
      (RecoveryComponents.recover chart rs hrs base domain received A) :=
  AgreementRecovery.Tower.recoverAgreement_exact_of_coverage base ι domain received k A hAk
    (RecoveryComponents.materializeComponents chart rs hrs) (by
      intro p hd ha
      obtain ⟨r, hr, out, u, v, ho, hp, hpoly⟩ := hcover p hd ha
      exact representedBy_of_materialized_point chart rs hrs base ι r out hr ho u v hp p hpoly)

/-- Under denominator regularity, geometric source coverage alone suffices. The constructor
must still prove the displayed rational polynomial identity for every wanted message. -/
theorem recover_exact_of_geometric_coverage
    (chart : ChartData E 1 k) (hregular : DenominatorRegular chart)
    (rs : List (TowerRepresentation (F := E))) (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width)
    (hopen : ∀ r ∈ rs, DenominatorUnits.OnOpenChart chart r)
    (base : F →+* E) (ι : E →+* L) (domain : Fin n ↪ F) (received : Fin n → F)
    (A : ℕ) (hAk : k ≤ A)
    (hcover : ∀ p : F[X], p.degree < k → A ≤ Code.agree (evalOnPoints domain p) received →
      ∃ r ∈ rs, ∃ u v, r.Point ι u v ∧
        rationalPolynomial chart ι u v = p.map (ι.comp base)) :
    ExactOutput domain received k A
      (RecoveryComponents.recover chart rs hrs base domain received A) :=
  AgreementRecovery.Tower.recoverAgreement_exact_of_coverage base ι domain received k A hAk
    (RecoveryComponents.materializeComponents chart rs hrs) (by
      intro p hd ha
      obtain ⟨r, hr, u, v, hp, hpoly⟩ := hcover p hd ha
      exact representedBy_of_regular_point chart hregular rs hrs hopen base ι r hr u v hp p hpoly)

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.Coverage
