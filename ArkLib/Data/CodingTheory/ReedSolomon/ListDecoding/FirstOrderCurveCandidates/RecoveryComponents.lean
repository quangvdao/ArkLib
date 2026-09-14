/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.DenominatorUnits
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.Tower

/-!
# Executable materialized components for agreement recovery

Each input weak tower is materialized using its actual chart denominator. A successful result
receives the erased weak well-formedness certificate required by recovery. Failed inversions
are explicit omissions; denominator regularity on the open chart proves no input is omitted.
This is an algebraic packet bridge, not a claim that the input towers cover all wanted messages.
Stored numerator order is preserved. Recovery interprets that list in descending Horner order;
identifying it with a centered Taylor message requires a separate order/center conversion proof.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.RecoveryComponents

open CompPoly
open ReedSolomon.HiddenDerivative.FastTaylor

variable {E : Type} [Field E] [BEq E] [LawfulBEq E] [DecidableEq E] {k width : ℕ}

/-- Execute materialization in order and attach only checked canonical-payload certificates. -/
def materializeComponents (chart : ChartData E 1 k) :
    (rs : List (TowerRepresentation (F := E))) →
    (∀ r ∈ rs, r.NonreducedWellFormed width) → List (AgreementRecovery.Tower.Component E k)
  | [], _ => []
  | r :: rs, hrs =>
      let rest := materializeComponents chart rs (fun a ha => hrs a (List.mem_cons_of_mem _ ha))
      match ho : MaterializeChart.run chart r with
      | none => rest
      | some out =>
          ⟨out, (MaterializeChart.run_shape chart r out
            (hrs r (List.mem_cons_self)) ho).2.2⟩ :: rest

/-- Component membership records exactly one successful run on an actual input tower. -/
theorem mem_materializeComponents_iff (chart : ChartData E 1 k)
    (rs : List (TowerRepresentation (F := E))) (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width)
    (c : AgreementRecovery.Tower.Component E k) :
    c ∈ materializeComponents chart rs hrs ↔
      ∃ r ∈ rs, MaterializeChart.run chart r = some c.val := by
  induction rs with
  | nil => simp [materializeComponents]
  | cons r rs ih =>
      simp only [materializeComponents]
      split
      · rename_i ho
        rw [ih]
        simp [ho]
      · rename_i out ho
        rw [List.mem_cons, ih]
        simp [ho, Subtype.ext_iff, eq_comm]

/-- Regularity on the open chart prevents every possible materialization omission. -/
theorem materializeComponents_length (chart : ChartData E 1 k)
    (hregular : DenominatorRegular chart) (rs : List (TowerRepresentation (F := E)))
    (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width)
    (hopen : ∀ r ∈ rs, DenominatorUnits.OnOpenChart chart r) :
    (materializeComponents chart rs hrs).length = rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      obtain ⟨out, ho, _⟩ := DenominatorUnits.materialize_exists chart hregular r
        (hrs r List.mem_cons_self) (hopen r List.mem_cons_self)
      simp only [materializeComponents]
      split
      · rename_i hn
        rw [ho] at hn
        contradiction
      · simp only [List.length_cons]
        congr 1
        exact ih (fun a ha => hrs a (List.mem_cons_of_mem _ ha))
          (fun a ha => hopen a (List.mem_cons_of_mem _ ha))

/-- Every input produces an actual output component under regularity, including duplicates. -/
theorem materializeComponents_complete (chart : ChartData E 1 k)
    (hregular : DenominatorRegular chart) (rs : List (TowerRepresentation (F := E)))
    (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width)
    (hopen : ∀ r ∈ rs, DenominatorUnits.OnOpenChart chart r)
    (r : TowerRepresentation (F := E)) (hr : r ∈ rs) :
    ∃ c ∈ materializeComponents chart rs hrs, MaterializeChart.run chart r = some c.val := by
  obtain ⟨out, ho, _, _, hw⟩ := DenominatorUnits.materialize_exists chart hregular r
    (hrs r hr) (hopen r hr)
  exact ⟨⟨out, hw⟩, (mem_materializeComponents_iff chart rs hrs _).mpr ⟨r, hr, ho⟩, ho⟩

/-- Feed the actual localized `FilterCore` output into the materializing component bridge. -/
def fromFilter (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (A : ℕ)
    (gs : List (CPolynomial (CPolynomial E))) (out : FilterCore.Trace E)
    (hout : FilterCore.run p inverse A k (chartPolynomials chart).equation gs = some out)
    (G : CPolynomial E) (hG : out.base = some G) (hGpos : 0 < G.natDegree)
    (hh : (chartPolynomials chart).equation.monic)
    (hhpos : 0 < (TowerRepresentation.reduceBase G (chartPolynomials chart).equation).natDegree) :
    List (AgreementRecovery.Tower.Component E k) :=
  materializeComponents chart
    (TowerCore.fromFilter p inverse hinverse A k (chartPolynomials chart).equation gs out hout G hG
      hGpos hh hhpos (chartPolynomials chart).separant).towers
    (fun child hc => TowerCore.fromFilter_wellFormed p inverse hinverse A k
      (chartPolynomials chart).equation gs out hout G hG hGpos hh hhpos
      (chartPolynomials chart).separant child hc)

/-- No localized filter child is lost when the chart denominator is regular. -/
theorem fromFilter_length (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (hregular : DenominatorRegular chart) (A : ℕ)
    (gs : List (CPolynomial (CPolynomial E))) (out : FilterCore.Trace E)
    (hout : FilterCore.run p inverse A k (chartPolynomials chart).equation gs = some out)
    (G : CPolynomial E) (hG : out.base = some G) (hGpos : 0 < G.natDegree)
    (hh : (chartPolynomials chart).equation.monic)
    (hhpos : 0 < (TowerRepresentation.reduceBase G (chartPolynomials chart).equation).natDegree) :
    (fromFilter p inverse hinverse chart A gs out hout G hG hGpos hh hhpos).length =
      (TowerCore.fromFilter p inverse hinverse A k
        (chartPolynomials chart).equation gs out hout G hG
        hGpos hh hhpos (chartPolynomials chart).separant).towers.length := by
  apply materializeComponents_length chart hregular
  intro child hc
  exact DenominatorUnits.fromFilter_onOpenChart p inverse hinverse chart A gs out hout G hG
    hGpos hh hhpos child hc

/-- Thin executable facade: materialize supplied parameter towers, then run checked recovery. -/
def recover {F : Type} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (chart : ChartData E 1 k) (rs : List (TowerRepresentation (F := E)))
    (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F) (A : ℕ) : List (List F) :=
  AgreementRecovery.Tower.recoverAgreement base domain received k A
    (materializeComponents chart rs hrs)

/-- Returned vectors pass the full word check; this does not assert constructor coverage. -/
theorem mem_recover_properties
    {F : Type} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (chart : ChartData E 1 k) (rs : List (TowerRepresentation (F := E)))
    (hrs : ∀ r ∈ rs, r.NonreducedWellFormed width)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F) (A : ℕ) (cs : List F)
    (hcs : cs ∈ recover chart rs hrs base domain received A) :
    cs.length = k ∧ (Polynomial.JetHornerMachine.coefficientPolynomial cs).degree < k ∧
      A ≤ Code.agree
        (evalOnPoints domain
          (Polynomial.JetHornerMachine.coefficientPolynomial cs)) received :=
  AgreementRecovery.Tower.mem_recoverAgreement_properties base domain received k A
    (materializeComponents chart rs hrs) cs hcs

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.RecoveryComponents
