/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.FilterCore
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.LocalizeFiber

/-!
# Parameter towers after the finite base filter

This adapter constructs only parameter algebras: its coefficient payload is empty, not a
purported recovered message. It reduces the supplied open-curve equation modulo the retained
base and localizes the resulting weak tower without radicalizing its fiber. Positive base and
reduced fiber degrees are explicit prerequisites. No denominator inversion, component removal,
message materialization, or candidate-coverage assertion is made here.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.TowerCore

open CompPoly TowerRepresentation

variable {E : Type} [Field E] [BEq E] [LawfulBEq E]

local instance : DecidableEq E := instDecidableEqOfLawfulBEq

/-- Every retained filter base has positive degree: the unit threshold was already discarded. -/
theorem filterBase_positive (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E)))
    (out : FilterCore.Trace E) (hout : FilterCore.run p inverse A k h gs = some out)
    (G : CPolynomial E) (hG : out.base = some G) : 0 < G.natDegree := by
  have hm := (FilterCore.run_threshold_properties p inverse A k h gs out hout).2.1
  obtain ⟨cs, H, _, _, rfl⟩ := FilterCore.run_provenance p inverse A k h gs out hout
  obtain ⟨hH, rfl⟩ := FilterCore.finish_base_some p inverse cs H G hG
  have props := CPolynomial.CharacteristicSafeRadical.radical_monic_associated
    p inverse hinverse H hm
  apply Nat.pos_of_ne_zero
  intro hz
  have hone : (CPolynomial.CharacteristicSafeRadical.radical p inverse H).toPoly = 1 :=
    Polynomial.eq_one_of_monic_natDegree_zero ((CPolynomial.monic_toPoly_iff _).mp props.1)
      (by simpa only [CPolynomial.natDegree_toPoly] using hz)
  obtain ⟨n, hn⟩ := UniqueFactorizationMonoid.exists_dvd_radical_self_pow
    ((CPolynomial.monic_toPoly_iff H).mp hm).ne_zero
  have hdvd := hn.trans (pow_dvd_pow_of_dvd props.2.dvd' n)
  rw [hone, one_pow] at hdvd
  apply hH
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.toPoly_one]
  exact ((CPolynomial.monic_toPoly_iff H).mp hm).eq_one_of_isUnit (isUnit_of_dvd_one hdvd)

/-- The unrecovered parameter algebra, with no message coefficient payload. -/
def parameterTower (G : CPolynomial E) (h : CPolynomial (CPolynomial E)) :
    TowerRepresentation (F := E) :=
  ⟨G, reduceBase G h, []⟩

/-- The reduced-fiber positivity prerequisite follows from the original monic curve degree. -/
theorem reducedFiber_positive (G : CPolynomial E) (h : CPolynomial (CPolynomial E))
    (hG : G.monic) (hGpos : 0 < G.natDegree) (hh : h.monic) (hhpos : 0 < h.natDegree) :
    0 < (reduceBase G h).natDegree := by
  rwa [TowerAlgebra.natDegree_reduceBase G hG hGpos h hh]

/-- Canonical reduction supplies the weak tower contract; fiber squarefreeness is unnecessary. -/
theorem parameterTower_wellFormed (G : CPolynomial E)
    (h : CPolynomial (CPolynomial E)) (hG : G.monic) (hGs : Squarefree G.toPoly)
    (hGpos : 0 < G.natDegree) (hh : h.monic)
    (hhpos : 0 < (reduceBase G h).natDegree) :
    (parameterTower G h).NonreducedWellFormed 0 := by
  exact ⟨hG, hGs, hGpos, monic_reduceBase hG hGpos hh, hhpos,
    baseReduced_reduceBase hG h, rfl, by simp [parameterTower]⟩

/-- Parameter points are exactly simultaneous roots of the base and original curve equation. -/
theorem parameterTower_point_iff (G : CPolynomial E)
    (h : CPolynomial (CPolynomial E)) (hG : G.monic)
    {K : Type} [Field K] (phi : E →+* K) (u v : K) :
    (parameterTower G h).Point phi u v ↔
      G.toPoly.eval₂ phi u = 0 ∧ evalNested h phi u v = 0 := by
  change (G.toPoly.eval₂ phi u = 0 ∧ evalNested (reduceBase G h) phi u v = 0) ↔ _
  constructor
  · rintro ⟨hu, hv⟩
    exact ⟨hu, (evalNested_reduceBase phi u v hG hu h) ▸ hv⟩
  · rintro ⟨hu, hv⟩
    exact ⟨hu, (evalNested_reduceBase phi u v hG hu h).symm ▸ hv⟩

/-- Actual filter trace accompanies the localized parameter algebras unchanged. -/
structure Output (E : Type) [Field E] [BEq E] [LawfulBEq E] where
  trace : FilterCore.Trace E
  towers : List (TowerRepresentation (F := E))

/-- Consume a successful filter base, retaining all fiber multiplicities during localization. -/
def fromFilter (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E)))
    (out : FilterCore.Trace E) (hout : FilterCore.run p inverse A k h gs = some out)
    (G : CPolynomial E) (hG : out.base = some G)
    (hGpos : 0 < G.natDegree) (hh : h.monic)
    (hhpos : 0 < (reduceBase G h).natDegree) (s : CPolynomial (CPolynomial E)) : Output E :=
  let props := FilterCore.run_base_squarefree_monic p inverse hinverse A k h gs out hout G hG
  ⟨out, TowerAlgebra.localizeFiber (parameterTower G h) s
    (parameterTower_wellFormed G h props.2 props.1 hGpos hh hhpos)⟩

/-- The complete coefficient/threshold/base trace is retained verbatim. -/
theorem fromFilter_trace (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E)))
    (out : FilterCore.Trace E) (hout : FilterCore.run p inverse A k h gs = some out)
    (G : CPolynomial E) (hG : out.base = some G)
    (hGpos : 0 < G.natDegree) (hh : h.monic)
    (hhpos : 0 < (reduceBase G h).natDegree) (s : CPolynomial (CPolynomial E)) :
    (fromFilter p inverse hinverse A k h gs out hout G hG hGpos hh hhpos s).trace = out := rfl

/-- All output algebras satisfy the weak contract, with the honestly empty message payload. -/
theorem fromFilter_wellFormed (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E)))
    (out : FilterCore.Trace E) (hout : FilterCore.run p inverse A k h gs = some out)
    (G : CPolynomial E) (hG : out.base = some G)
    (hGpos : 0 < G.natDegree) (hh : h.monic)
    (hhpos : 0 < (reduceBase G h).natDegree) (s : CPolynomial (CPolynomial E))
    (child : TowerRepresentation (F := E))
    (hc : child ∈ (fromFilter p inverse hinverse A k h gs out hout G hG
      hGpos hh hhpos s).towers) : child.NonreducedWellFormed 0 := by
  exact TowerAlgebra.localizeFiber_nonreducedWellFormed _ _ _ child hc

/-- Localized points are exactly threshold roots lying on the supplied open curve where `s ≠ 0`.
This is parameter-point semantics, not an agreement or candidate-coverage theorem. -/
theorem fromFilter_point_iff (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E)))
    (out : FilterCore.Trace E) (hout : FilterCore.run p inverse A k h gs = some out)
    (G : CPolynomial E) (hG : out.base = some G)
    (hGpos : 0 < G.natDegree) (hh : h.monic)
    (hhpos : 0 < (reduceBase G h).natDegree) (s : CPolynomial (CPolynomial E))
    {K : Type} [Field K] (phi : E →+* K) (u v : K) :
    (∃ child ∈ (fromFilter p inverse hinverse A k h gs out hout G hG
      hGpos hh hhpos s).towers, child.Point phi u v) ↔
      (out.thresholdPolynomial.toPoly.eval₂ phi u = 0 ∧ evalNested h phi u v = 0) ∧
        evalNested s phi u v ≠ 0 := by
  have props := FilterCore.run_base_squarefree_monic p inverse hinverse A k h gs out hout G hG
  change (∃ child ∈ TowerAlgebra.localizeFiber _ _ _, child.Point phi u v) ↔ _
  rw [TowerAlgebra.localizeFiber_point_iff, parameterTower_point_iff G h props.2,
    FilterCore.run_base_eval₂_eq_zero_iff p inverse hinverse A k h gs out hout G hG]

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.TowerCore
