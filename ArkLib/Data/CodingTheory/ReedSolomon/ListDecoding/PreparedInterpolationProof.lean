/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.PreparedDecoderCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.PreparedDecoderMachine
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.StageInputExecution

/-!
# Exact prepared decoding after actual successful interpolation

The certificate supplies agreement-to-root completeness. The scalar allocator, root scan and
collector execute their actual programs, and their completed traces compose in the existing
prepared driver. No semantic output or agreement-to-output callback is assumed.
-/

namespace ReedSolomon.ListDecoding.PreparedInterpolationProof

open Polynomial JetHornerMachine HiddenDerivative PreparedDecoderCertificate

variable {F : Type*} [Field F] [DecidableEq F]

/-- The prepared driver returns each target-degree agreeing base polynomial exactly once.
The premise is a successful direct interpolation attempt; ambient bounds are explicit.
All three later child executions are proved using the existing pipeline.
The returned cost is the actual trace charge, with no claimed whole-instance majorant. -/
theorem run_exact {D k d m A n L : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (interpolant : NonzeroInterpolationMachine.Output F)
    (hr : (NonzeroInterpolationMachine.run D d m A
      (List.ofFn fun i ↦ (domain i, received i))).1 = some interpolant)
    (hdepth : d ≤ D) (hk : k ≤ D + 1)
    (a : F) (ha : ¬IsSquare a) (alphabet samples : List (QuadraticAlgebra F a 0))
    (points : Fin L ↪ QuadraticAlgebra F a 0)
    (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hall : ∀ x : QuadraticAlgebra F a 0, x ∈ alphabet) (hn : alphabet.Nodup)
    (hchar : IsBelowCharacteristic D
      (NonzeroInterpolationMachine.sourceOutput (d := d) D m A interpolant))
    (hweight : differentialWeightedDegree D
      (NonzeroInterpolationMachine.sourceOutput (d := d) D m A interpolant) < L) :
    let input : PreparedDecoderMachine.Input F a :=
      ⟨alphabet, samples, List.ofFn (fun i ↦ (domain i, received i)), d, D, L, k, A⟩
    ∃ steps cost out,
      PreparedDecoderMachine.Trace input ha steps (.start interpolant.terms) cost
        (.done (some out)) ∧
      PreparedDecoderMachine.runFuel input ha steps (.start interpolant.terms) =
        (.done (some out), cost) ∧
      (out.map coefficientPolynomial).Nodup ∧ out.Nodup ∧
      (∀ f : F[X], f ∈ out.map coefficientPolynomial ↔
        f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received) ∧
      (∀ cs : List F, cs ∈ out ↔ cs.length = k ∧
        (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received) := by
  let : Fact (∀ r : F, r ^ 2 ≠ a + 0 * r) := ⟨by
    intro r he
    apply ha
    exact ⟨r, by simpa only [zero_mul, add_zero, pow_two] using he.symm⟩⟩
  let input : PreparedDecoderMachine.Input F a :=
    ⟨alphabet, samples, List.ofFn (fun i ↦ (domain i, received i)), d, D, L, k, A⟩
  let Q := NonzeroInterpolationMachine.sourceOutput (d := d) D m A interpolant
  let EQ := MvPolynomial.map (algebraMap F (QuadraticAlgebra F a 0)) Q
  let ets := MvPolynomial.QuadraticInputMachine.embedded (a := a) interpolant.terms
  let ri := PreparedDecoderMachine.rootInput input ets
  obtain ⟨result, cost, he, _hcost, hcert⟩ :=
    NonzeroInterpolationMachine.attempt_complete (d := d) D m A
      (List.ofFn fun i ↦ (domain i, received i))
  have he' := congrArg Prod.fst he
  rw [hr] at he'
  have hc := hcert interpolant he'.symm
  have hl := attempt_layout D d m A _ interpolant hr
  have hrep : MvPolynomial.EvaluationMachine.sparsePolynomial ets =
      MvPolynomial.rename HighestJetTransport.encodeJet EQ :=
    embedded_representation _ interpolant hc a
  have hQne : Q ≠ 0 := by
    intro hz
    have he := hc.2.2.2.2.2.2.1
    have hnz := hc.2.2.2.2.2.2.2.1
    rw [show NonzeroInterpolationMachine.sourceOutput (d := d) D m A
      interpolant = 0 from hz, map_zero] at he
    exact hnz he
  have hEQne : EQ ≠ 0 := by
    intro hz
    apply hQne
    exact MvPolynomial.map_injective _
      (algebraMap F (QuadraticAlgebra F a 0)).injective (by simpa [EQ] using hz)
  have hEQchar : IsBelowCharacteristic D EQ :=
    (isBelowCharacteristic_map_iff Q D).mpr hchar
  have hEQweight : differentialWeightedDegree D EQ < L := by
    simpa only [EQ, differentialWeightedDegree_map_eq _
      (algebraMap F (QuadraticAlgebra F a 0)).injective Q] using hweight
  have hElayout : MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (d + 2)) ets :=
    MvPolynomial.QuadraticInputMachine.embedded_layout _ _ hl
  obtain ⟨cc, hconvert, _hcc⟩ := MvPolynomial.QuadraticInputMachine.scan_trace
    interpolant.terms ([] : List (MvPolynomial.QuadraticInputMachine.Term
      (QuadraticAlgebra F a 0)))
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at hconvert
  obtain ⟨stages, records, cr, hchain, _hstagecount, hrun, _hvisited, hspec,
      _hwidth, _hcount, _hrootcost⟩ := StageRootsMachine.execution_input_budget ri points samples
    hsamples (List.length_pos_of_mem (hall 0)) hdepth (jetTotalDegree EQ) EQ
    hElayout hrep hEQne hEQchar.2 le_rfl hEQweight
  obtain ⟨nr, _hnr, hroots⟩ := StageRootsMachine.runFuel_refines ri D L
    (StageRootsMachine.inputFuel ri D L samples.length (jetTotalDegree EQ))
    (.start samples)
  rw [hrun] at hroots
  obtain ⟨out, co, hcollectrun, hout, _hlen, hdup, hvecdup, hwidth, hpoly, _hcost⟩ :=
    CanonicalOutputProof.stage_runFuel_correct ri points samples hsamples hall hn hdepth hrep
      hchain hEQne hEQchar hEQweight hspec hk domain received (A := A)
  obtain ⟨no, _hno, hcollect⟩ := CanonicalOutputMachine.runFuel_refines d (D + 1) k A
    (CanonicalOutputMachine.fuel d samples (D + 1) k n records) samples
    (List.ofFn fun i ↦ (domain i, received i)) (.start records)
  rw [hcollectrun] at hcollect
  have hpipeline := PreparedDecoderMachine.pipeline_trace input ha interpolant.terms ets
    records out (2 * interpolant.terms.length + 3) nr no co cc cr hconvert hroots hcollect
  refine ⟨_, _, out, hpipeline, ?_, hdup, hvecdup, ?_, ?_⟩
  · simpa only [Nat.add_zero] using hpipeline.runFuel_done 0
  · intro f
    rw [hpoly]
    constructor
    · exact fun h ↦ ⟨h.1, h.2.1⟩
    · rintro ⟨hd, hagree⟩
      exact ⟨hd, hagree, certified_embedded_root _ domain received interpolant hc hk
        f hd hagree⟩
  · intro cs
    constructor
    · intro hm
      have hf := (hpoly _).mp (List.mem_map.mpr ⟨cs, hm, rfl⟩)
      exact ⟨hwidth cs hm, hf.1, hf.2.1⟩
    · rintro ⟨hw, hd, hagree⟩
      have hf := (hpoly _).mpr ⟨hd, hagree, certified_embedded_root _ domain received
        interpolant hc hk (coefficientPolynomial cs) hd hagree⟩
      obtain ⟨bs, hb, he⟩ := List.mem_map.mp hf
      have heq := CanonicalRootSelection.coefficients_unique bs cs
        ((hwidth bs hb).trans hw.symm) he
      simpa only [heq] using hb

end ReedSolomon.ListDecoding.PreparedInterpolationProof
