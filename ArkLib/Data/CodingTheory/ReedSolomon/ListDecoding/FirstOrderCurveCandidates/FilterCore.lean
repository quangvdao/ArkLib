/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ResultantFilter
public import ArkLib.Data.Polynomial.PolynomialThreshold.BooleanNetwork
public import ArkLib.Data.Polynomial.CharacteristicSafeRadical

/-!
# Finite base filter for an already prepared open curve

Each received position contributes its lowest characteristic-polynomial coefficient. The fixed
bitonic network selects threshold `A-k+1`. A unit threshold returns no base; otherwise exactly
one characteristic-safe radical supplies the squarefree base modulus.

The trace records actual computed coefficients and the threshold before radicalization. This
core does not remove closed curve components, localize fibers, or assert candidate coverage.
The equation must already be the monic equation of the intended open curve when interpreting
the resulting base geometrically.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.FilterCore

open CompPoly

variable {E : Type} [Field E] [BEq E] [LawfulBEq E]

/-- Scan all residuals in received-position order, without dropping a failed scan. -/
def coefficients? (h : CPolynomial (CPolynomial E)) :
    List (CPolynomial (CPolynomial E)) → Option (List (CPolynomial E))
  | [] => some []
  | g :: gs => do
      let c ← residualFilter? h g
      let cs ← coefficients? h gs
      pure (c :: cs)

/-- Every per-position scan succeeds, preserves the position count, and returns a monic row. -/
theorem coefficients?_exists (h : CPolynomial (CPolynomial E))
    (gs : List (CPolynomial (CPolynomial E))) :
    ∃ cs, coefficients? h gs = some cs ∧ cs.length = gs.length ∧
      ∀ c ∈ cs, c.monic := by
  induction gs with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons g gs ih =>
    obtain ⟨c, hc⟩ := residualFilter?_exists h g
    obtain ⟨cs, hcs, hlen, hm⟩ := ih
    refine ⟨c :: cs, ?_, by simp [hlen], ?_⟩
    · simp [coefficients?, hc, hcs]
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact residualFilter?_monic h g a hc
      · exact hm a ha

/-- A successful row scan exposes its exact count and monicity. -/
theorem coefficients?_properties (h : CPolynomial (CPolynomial E))
    (gs : List (CPolynomial (CPolynomial E))) (cs : List (CPolynomial E))
    (hc : coefficients? h gs = some cs) :
    cs.length = gs.length ∧ ∀ c ∈ cs, c.monic := by
  obtain ⟨actual, ha, hlen, hm⟩ := coefficients?_exists h gs
  have heq : actual = cs := Option.some.inj (ha.symm.trans hc)
  simpa only [heq] using And.intro hlen hm

omit [BEq E] [LawfulBEq E] in
private theorem wires_all_mem {d : ℕ}
    (a : CPolynomial.PolynomialThreshold.Wires E d) (P : CPolynomial E → Prop)
    (ha : a.All P) : ∀ c ∈ a.toList, P c := by
  induction a with
  | leaf a =>
    simpa [CPolynomial.PolynomialThreshold.Wires.toList,
      CPolynomial.PolynomialThreshold.Wires.All] using ha
  | node a b ia ib =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ia ha.1 c hc
    · exact ib ha.2 c hc

/-- The selected threshold wire is monic whenever all per-position polynomials are monic. -/
theorem threshold_monic (cs : List (CPolynomial E)) (hm : ∀ c ∈ cs, c.monic)
    (t : ℕ) (H : CPolynomial E)
    (hH : CPolynomial.PolynomialThreshold.threshold cs.toArray t = some H) : H.monic := by
  unfold CPolynomial.PolynomialThreshold.threshold at hH
  split at hH
  · have hall := CPolynomial.PolynomialThreshold.sort_monic true _
      (CPolynomial.PolynomialThreshold.padded_monic cs.toArray
        (fun c hc => hm c (by simpa using hc))
        (CPolynomial.PolynomialThreshold.paddingDepth cs.toArray.size) 0)
    exact wires_all_mem _ _ hall H (List.mem_of_getElem? hH)
  · contradiction

/-- Intermediate state of the new coefficient-threshold-radical path. -/
structure Trace (E : Type*) [Field E] [BEq E] [LawfulBEq E] where
  coefficients : List (CPolynomial E)
  thresholdPolynomial : CPolynomial E
  base : Option (CPolynomial E)

/-- Empty thresholds return no base. The nonempty branch executes one radical call. -/
def finish (p : ℕ) [Fact p.Prime] (inverse : E → E)
    (cs : List (CPolynomial E)) (H : CPolynomial E) : Trace E :=
  { coefficients := cs
    thresholdPolynomial := H
    base := if H == 1 then none
      else some (CPolynomial.CharacteristicSafeRadical.radical p inverse H) }

/-- Execute the finite-base core directly from the prepared equation and residual rows. -/
def run (p : ℕ) [Fact p.Prime] (inverse : E → E) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E))) :
    Option (Trace E) :=
  match coefficients? h gs with
  | none => none
  | some cs =>
    match CPolynomial.PolynomialThreshold.threshold cs.toArray (A - k + 1) with
    | none => none
    | some H => some (finish p inverse cs H)

/-- The coefficient and network stages succeed under the paper's threshold range. -/
theorem run_exists (p : ℕ) [Fact p.Prime] (inverse : E → E) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E)))
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ gs.length) :
    ∃ out, run p inverse A k h gs = some out := by
  obtain ⟨cs, hc, hlen, _⟩ := coefficients?_exists h gs
  obtain ⟨H, hH⟩ := CPolynomial.PolynomialThreshold.threshold_exists cs.toArray (A - k + 1)
    (by omega) (by simp only [List.size_toArray]; omega)
  exact ⟨finish p inverse cs H, by simp [run, hc, hH]⟩

/-- Successful execution records the actual coefficient scan and actual threshold wire. -/
theorem run_provenance (p : ℕ) [Fact p.Prime] (inverse : E → E) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E)))
    (out : Trace E) (hout : run p inverse A k h gs = some out) :
    ∃ cs H, coefficients? h gs = some cs ∧
      CPolynomial.PolynomialThreshold.threshold cs.toArray (A - k + 1) = some H ∧
      out = finish p inverse cs H := by
  cases hc : coefficients? h gs with
  | none => simp [run, hc] at hout
  | some cs =>
    cases hH : CPolynomial.PolynomialThreshold.threshold cs.toArray (A - k + 1) with
    | none => simp [run, hc, hH] at hout
    | some H =>
      exact ⟨cs, H, rfl, hH, (Option.some.inj (by simpa [run, hc, hH] using hout)).symm⟩

/-- The executed threshold is monic and nonzero, and rows still count distinct positions. -/
theorem run_threshold_properties (p : ℕ) [Fact p.Prime] (inverse : E → E) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E)))
    (out : Trace E) (hout : run p inverse A k h gs = some out) :
    out.coefficients.length = gs.length ∧ out.thresholdPolynomial.monic ∧
      out.thresholdPolynomial ≠ 0 := by
  obtain ⟨cs, H, hc, hH, rfl⟩ := run_provenance p inverse A k h gs out hout
  obtain ⟨hlen, hm⟩ := coefficients?_properties h gs cs hc
  have hmonic := threshold_monic cs hm _ H hH
  exact ⟨hlen, hmonic,
    (CPolynomial.toPoly_eq_zero_iff H).not.mp
      ((CPolynomial.monic_toPoly_iff H).mp hmonic).ne_zero⟩

/-- The finalization state has no base exactly when the executed threshold is one. -/
theorem finish_base_none_iff (p : ℕ) [Fact p.Prime] (inverse : E → E)
    (cs : List (CPolynomial E)) (H : CPolynomial E) :
    (finish p inverse cs H).base = none ↔ H = 1 := by
  simp [finish]

/-- Every retained base is the radical of the recorded threshold. -/
theorem finish_base_some (p : ℕ) [Fact p.Prime] (inverse : E → E)
    (cs : List (CPolynomial E)) (H G : CPolynomial E)
    (hG : (finish p inverse cs H).base = some G) :
    H ≠ 1 ∧ G = CPolynomial.CharacteristicSafeRadical.radical p inverse H := by
  simp only [finish] at hG
  split at hG
  · contradiction
  · rename_i hn
    exact ⟨by simpa using hn, (Option.some.inj hG).symm⟩

/-- Retained bases are monic and squarefree under the supplied inverse-Frobenius laws. -/
theorem run_base_squarefree_monic (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E)))
    (out : Trace E) (hout : run p inverse A k h gs = some out)
    (G : CPolynomial E) (hG : out.base = some G) : Squarefree G.toPoly ∧ G.monic := by
  have hm := (run_threshold_properties p inverse A k h gs out hout).2.1
  obtain ⟨cs, H, _, _, rfl⟩ := run_provenance p inverse A k h gs out hout
  obtain ⟨_, rfl⟩ := finish_base_some p inverse cs H G hG
  exact CPolynomial.CharacteristicSafeRadical.radical_squarefree_monic p inverse hinverse H hm

/-- Radicalization preserves precisely the threshold roots over any extension field. -/
theorem run_base_eval₂_eq_zero_iff (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E)))
    (out : Trace E) (hout : run p inverse A k h gs = some out)
    (G : CPolynomial E) (hG : out.base = some G)
    {K : Type*} [Field K] (base : E →+* K) (x : K) :
    G.toPoly.eval₂ base x = 0 ↔ out.thresholdPolynomial.toPoly.eval₂ base x = 0 := by
  have hm := (run_threshold_properties p inverse A k h gs out hout).2.1
  obtain ⟨cs, H, _, _, rfl⟩ := run_provenance p inverse A k h gs out hout
  obtain ⟨_, rfl⟩ := finish_base_some p inverse cs H G hG
  exact CPolynomial.CharacteristicSafeRadical.radical_eval₂_eq_zero_iff
    p inverse hinverse H hm base x

/-- The empty-base branch is exactly the executed unit-threshold branch. -/
theorem run_base_none_iff (p : ℕ) [Fact p.Prime] (inverse : E → E) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E)))
    (out : Trace E) (hout : run p inverse A k h gs = some out) :
    out.base = none ↔ out.thresholdPolynomial = 1 := by
  obtain ⟨cs, H, _, _, rfl⟩ := run_provenance p inverse A k h gs out hout
  exact finish_base_none_iff p inverse cs H

open CPolynomial.PolynomialThreshold in
/-- A retained base detects at least `A-k+1` distinct coefficient rows, after arbitrary
field extension. This is a finite-base statement, not a curve candidate-cover assertion. -/
theorem run_base_root_positions_iff (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E)))
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ gs.length)
    (out : Trace E) (hout : run p inverse A k h gs = some out)
    (G : CPolynomial E) (hG : out.base = some G)
    {K : Type*} [Field K] (base : E →+* K) (x : K) :
    G.toPoly.eval₂ base x = 0 ↔ A - k + 1 ≤
      (vanishingPositions base x out.coefficients.toArray).card := by
  rw [run_base_eval₂_eq_zero_iff p inverse hinverse A k h gs out hout G hG base x]
  obtain ⟨cs, H, hc, hH, rfl⟩ := run_provenance p inverse A k h gs out hout
  obtain ⟨hlen, hm⟩ := coefficients?_properties h gs cs hc
  apply CPolynomial.PolynomialThreshold.threshold_root_positions_iff base x cs.toArray
    _ (A - k + 1) (by omega) (by simp only [List.size_toArray]; omega) H hH
  intro c hmem
  exact (CPolynomial.toPoly_eq_zero_iff c).not.mp
    ((CPolynomial.monic_toPoly_iff c).mp (hm c (by simpa using hmem))).ne_zero

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.FilterCore
