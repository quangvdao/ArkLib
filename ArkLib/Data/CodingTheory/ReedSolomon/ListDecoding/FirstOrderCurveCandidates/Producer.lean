/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.PreparedCoverage
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ComponentRemoval

/-! # Executable first-order curve candidate producer

The producer removes closed components, executes coefficient thresholding and radicalization,
localizes the retained fibers, and materializes their centered Taylor payloads. Empty retained
curves and unit thresholds return the empty family. Exact recovery is reduced to detection of
the concrete geometric source points by the executed filter.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.Producer

open CompPoly Polynomial TowerRepresentation TowerAlgebra
open ReedSolomon.HiddenDerivative.FastTaylor

variable {E : Type} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E] {k n : ℕ}

/-- Remove entire primary components supported on the actual chart separant. -/
def retained (chart : ChartData E 1 k) : CPolynomial (CPolynomial E) :=
  ComponentRemoval.retain (chartPolynomials chart).equation (chartPolynomials chart).separant
    (chartPolynomials chart).equation.natDegree

omit [DecidableEq E] in
theorem retained_monic (chart : ChartData E 1 k)
    (hh : (chartPolynomials chart).equation.monic) : (retained chart).monic :=
  ComponentRemoval.retain_monic _ _ _ hh

omit [DecidableEq E] in
theorem retained_dvd (chart : ChartData E 1 k)
    (hh : (chartPolynomials chart).equation.monic) :
    retained chart ∣ (chartPolynomials chart).equation := by
  refine ⟨ComponentRemoval.removed (chartPolynomials chart).equation
    (chartPolynomials chart).separant (chartPolynomials chart).equation.natDegree, ?_⟩
  rw [mul_comm]
  exact (ComponentRemoval.product _ _ _ hh).symm

/-- The computed family together with its actual base degree and structural dimension bound. -/
structure Output (E : Type) [Field E] [BEq E] [LawfulBEq E] (k fiberDegree : ℕ) where
  components : List (AgreementRecovery.Tower.Component E k)
  baseDegree : ℕ
  dimension_le : (components.map fun c => c.val.dimension).sum ≤ baseDegree * fiberDegree

def empty (fiberDegree : ℕ) : Output E k fiberDegree := ⟨[], 0, by simp⟩

/-- Execute the complete chart-local candidate construction. The residual list is passed in
received-position order; a failed threshold range is represented by an empty family. -/
def run (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (hh : (chartPolynomials chart).equation.monic)
    (A : ℕ) (gs : List (CPolynomial (CPolynomial E))) :
    Output E k (retained chart).natDegree :=
  if hpos : 0 < (retained chart).natDegree then
    match hout : FilterCore.run p inverse A k (retained chart) gs with
    | none => empty _
    | some out =>
        match hG : out.base with
        | none => empty _
        | some G =>
          let hGpos := TowerCore.filterBase_positive p inverse hinverse A k
            (retained chart) gs out hout G hG
          let hm := retained_monic chart hh
          let hGmonic := (FilterCore.run_base_squarefree_monic p inverse hinverse A k
            (retained chart) gs out hout G hG).2
          let hfpos := TowerCore.reducedFiber_positive G (retained chart) hGmonic hGpos hm hpos
          ⟨PreparedCoverage.fromFilter p inverse hinverse chart A (retained chart) gs out hout
              G hG hGpos hm hfpos, G.natDegree,
            PreparedCoverage.fromFilter_dimension_le p inverse hinverse chart A (retained chart)
              gs out hout G hG hGpos hm hfpos⟩
  else empty _

/-- The executed producer's total algebra dimension uses the computed radical base degree
and retained fiber degree. -/
theorem run_dimension_le (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (hh : (chartPolynomials chart).equation.monic)
    (A : ℕ) (gs : List (CPolynomial (CPolynomial E))) :
    ((run p inverse hinverse chart hh A gs).components.map fun c => c.val.dimension).sum ≤
      (run p inverse hinverse chart hh A gs).baseDegree * (retained chart).natDegree :=
  (run p inverse hinverse chart hh A gs).dimension_le

/-- The local geometric condition expected from the global component and agreement argument.
It refers to the actual filter run and source coordinates, without recovery components. -/
def WantedPointDetected (p : ℕ) [Fact p.Prime] (inverse : E → E)
    (chart : ChartData E 1 k) (A : ℕ) (gs : List (CPolynomial (CPolynomial E))) (P : E[X]) : Prop :=
  ∃ out u v, FilterCore.run p inverse A k (retained chart) gs = some out ∧
    out.thresholdPolynomial.toPoly.eval₂ (RingHom.id E) u = 0 ∧
    evalNested (retained chart) (RingHom.id E) u v = 0 ∧
    evalNested (chartPolynomials chart).separant (RingHom.id E) u v ≠ 0 ∧
    ∀ j : Fin k, evalNested ((chartPolynomials chart).numerators j) (RingHom.id E) u v /
      evalNested (chartPolynomials chart).denominator (RingHom.id E) u v =
        (taylor chart.center P).coeff j

omit [DecidableEq E] in
private theorem degree_pos_of_point (h : CPolynomial (CPolynomial E)) (hm : h.monic)
    (u v : E) (hz : evalNested h (RingHom.id E) u v = 0) : 0 < h.natDegree := by
  apply Nat.pos_of_ne_zero
  intro hd
  have hone : h.toPoly = 1 := Polynomial.eq_one_of_monic_natDegree_zero
    ((CPolynomial.monic_toPoly_iff h).mp hm) (by simpa only [CPolynomial.natDegree_toPoly] using hd)
  have heq : h = 1 := CPolynomial.toPoly_injective (hone.trans CPolynomial.toPoly_one.symm)
  rw [heq, evalNested_one] at hz
  exact one_ne_zero hz

/-- Every detected source point enters an actual materialized producer component. -/
theorem representedBy_of_detected (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (hh : (chartPolynomials chart).equation.monic)
    (hregular : DenominatorRegular chart) (A : ℕ)
    (gs : List (CPolynomial (CPolynomial E))) (P : E[X]) (hd : P.degree < k)
    (hdet : WantedPointDetected p inverse chart A gs P) :
    AgreementRecovery.Tower.RepresentedBy (RingHom.id E) (RingHom.id E) k
      (run p inverse hinverse chart hh A gs).components P := by
  obtain ⟨out, u, v, hout, ht, hz, hs, hc⟩ := hdet
  have hpos := degree_pos_of_point (retained chart) (retained_monic chart hh) u v hz
  have hb : out.base ≠ none := by
    intro hb
    have heq := (FilterCore.run_base_none_iff p inverse A k (retained chart) gs out hout).mp hb
    rw [heq, CPolynomial.toPoly_one, Polynomial.eval₂_one] at ht
    exact one_ne_zero ht
  obtain ⟨G, hG⟩ := Option.ne_none_iff_exists'.mp hb
  have hGpos := TowerCore.filterBase_positive p inverse hinverse A k
    (retained chart) gs out hout G hG
  have hm := retained_monic chart hh
  have hGmonic := (FilterCore.run_base_squarefree_monic p inverse hinverse A k
    (retained chart) gs out hout G hG).2
  have hfpos := TowerCore.reducedFiber_positive G (retained chart) hGmonic hGpos hm hpos
  obtain ⟨r, hr, hp⟩ := (TowerCore.fromFilter_point_iff p inverse hinverse A k
    (retained chart) gs out hout G hG hGpos hm hfpos (chartPolynomials chart).separant
    (RingHom.id E) u v).mpr ⟨⟨ht, hz⟩, hs⟩
  obtain ⟨raw, hraw, _⟩ := DenominatorUnits.materialize_exists chart hregular r
    (TowerCore.fromFilter_wellFormed p inverse hinverse A k (retained chart) gs out hout G hG
      hGpos hm hfpos (chartPolynomials chart).separant r hr)
    (PreparedCoverage.fromFilter_onOpenChart p inverse hinverse chart A (retained chart)
      (retained_dvd chart hh) gs out hout G hG hGpos hm hfpos r hr)
  have hrep := CenteredCoverage.representedBy_of_taylor_point chart _
    (TowerCore.fromFilter_wellFormed p inverse hinverse A k (retained chart) gs out hout G hG
      hGpos hm hfpos (chartPolynomials chart).separant) r raw hr hraw u v hp P hd hc
  unfold run
  rw [dif_pos hpos]
  split
  · rename_i hnone
    simp [hout] at hnone
  · rename_i actual hactual
    have heq : actual = out := Option.some.inj (hactual.symm.trans hout)
    subst actual
    split
    · rename_i hnone
      simp [hG] at hnone
    · rename_i actualG hactualG
      have heq : actualG = G := Option.some.inj (hactualG.symm.trans hG)
      subst actualG
      exact hrep

/-- Apply checked agreement recovery to the produced family. -/
def recover (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (hh : (chartPolynomials chart).equation.monic)
    (A : ℕ) (gs : List (CPolynomial (CPolynomial E)))
    (domain : Fin n ↪ E) (received : Fin n → E) : List (List E) :=
  AgreementRecovery.Tower.recoverAgreement (RingHom.id E) domain received k A
    (run p inverse hinverse chart hh A gs).components

/-- Concrete geometric point detection yields exact checked recovery. -/
theorem recover_exact (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (hh : (chartPolynomials chart).equation.monic)
    (hregular : DenominatorRegular chart) (A : ℕ) (hAk : k ≤ A)
    (gs : List (CPolynomial (CPolynomial E)))
    (domain : Fin n ↪ E) (received : Fin n → E)
    (hdetect : ∀ P : E[X], P.degree < k → A ≤ Code.agree (evalOnPoints domain P) received →
      WantedPointDetected p inverse chart A gs P) :
    ExactOutput domain received k A (recover p inverse hinverse chart hh A gs domain received) := by
  apply AgreementRecovery.Tower.recoverAgreement_exact_of_coverage
    (RingHom.id E) (RingHom.id E) domain received k A hAk
  intro P hd ha
  exact representedBy_of_detected p inverse hinverse chart hh hregular A gs P hd (hdetect P hd ha)

/-- Actual chart residuals retain the original received-position order. -/
def agreementRows (chart : ChartData E 1 k) (domain : Fin n ↪ E) (received : Fin n → E) :
    List (CPolynomial (CPolynomial E)) :=
  List.ofFn fun i => agreementPolynomial chart (domain i) (received i)

/-- Word-to-candidate facade, including construction of every cleared agreement residual. -/
def decode (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (hh : (chartPolynomials chart).equation.monic)
    (A : ℕ) (domain : Fin n ↪ E) (received : Fin n → E) : List (List E) :=
  recover p inverse hinverse chart hh A (agreementRows chart domain received) domain received

theorem decode_exact (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (hh : (chartPolynomials chart).equation.monic)
    (hregular : DenominatorRegular chart) (A : ℕ) (hAk : k ≤ A)
    (domain : Fin n ↪ E) (received : Fin n → E)
    (hdetect : ∀ P : E[X], P.degree < k → A ≤ Code.agree (evalOnPoints domain P) received →
      WantedPointDetected p inverse chart A (agreementRows chart domain received) P) :
    ExactOutput domain received k A (decode p inverse hinverse chart hh A domain received) :=
  recover_exact p inverse hinverse chart hh hregular A hAk _ domain received hdetect

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.Producer
