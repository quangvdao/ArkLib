/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.CoordinateStagesRefinement
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.StageRootsBounds

/-!
# Raw coordinate stage execution and its mathematical specification

The supplied coordinate terms and samples execute directly. Decoding occurs only in the logical
statement. The actual ordered records inherit the source stage specification, fixed coefficient
width, and count bound. The instruction budget has the original single alphabet exponent.
-/

namespace ReedSolomon.HiddenDerivative.QuadraticStageRootsMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (encode)

variable {F : Type*} [Field F] [DecidableEq F]

/-- Complete stage construction on raw pairs, with the same exact ordered records and one alphabet
exponent. The coordinate factor multiplies the total source fuel once. -/
theorem execution_correct (a : F) (ha : ¬IsSquare a) (input : Input F) (D L Δ : ℕ)
    (points : Fin L ↪ QuadraticAlgebra F a 0) (samples : List (Pair F)) :
    letI := fieldOfNonsquare a ha
    let source := mapInput (ArithmeticMachine.decode a) input
    ∀ Q : DifferentialPolynomial (QuadraticAlgebra F a 0) input.order,
      samples.map (ArithmeticMachine.decode a) = List.ofFn (fun i ↦ points i) →
      0 < input.alphabet.length → input.order ≤ D →
      MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (input.order + 2)) source.terms →
      MvPolynomial.EvaluationMachine.sparsePolynomial source.terms =
        MvPolynomial.rename HighestJetTransport.encodeJet Q → Q ≠ 0 →
      (∀ j, jetDegree Q j < ringChar (QuadraticAlgebra F a 0)) → jetTotalDegree Q ≤ Δ →
      differentialWeightedDegree D Q < L →
      let B := SeparantChainRefinement.budget Δ source.terms.length (input.order + 2)
        (MvPolynomial.PartialDerivativeMachine.inputMass source.terms)
      ∃ stages out steps c,
        SeparantChainRefinement.OrderedChain source.terms Q stages ∧ stages.length ≤ Δ + 1 ∧
        runFuel a input D L steps (.start samples) = (.done (some (mapRecords encode out)), c) ∧
        StageRootsMachine.Specification source D L (samples.map (ArithmeticMachine.decode a))
          stages [] out ∧
        (∀ record ∈ mapRecords encode out, record.coefficients.length = D + 1) ∧
        (mapRecords encode out).length ≤ stages.length * input.alphabet.length ^ (input.order + 2) ∧
        steps + c.total ≤ 4294967296 * (B + input.alphabet.length ^ (input.order + 2) *
          (stages.map (StageRootsMachine.fuelPolynomial source D L samples.length)).sum + 5) := by
  let := fieldOfNonsquare a ha
  let source := mapInput (ArithmeticMachine.decode a) input
  dsimp only
  intro Q hs hq hd hl hQ hn hc hdeg hw
  have hq' : 0 < source.alphabet.length := by simpa [source, mapInput] using hq
  obtain ⟨stages, out, sc, hchain, hlen, hr, hspec, hwidth, hcount, _⟩ :=
    StageRootsMachine.execution_correct source points (samples.map (ArithmeticMachine.decode a))
      hs hq' hd Δ Q hl hQ hn hc hdeg hw
  obtain ⟨steps, c, he, hb⟩ := start_run_lowering a ha input D L _ samples (some out) sc hr
  have hcount' := StageRootsMachine.count_single_exponent source hq' hchain
  have hf := StageRootsMachine.fuel_single_exponent source D L
    (samples.map (ArithmeticMachine.decode a)).length
    (SeparantChainRefinement.budget Δ source.terms.length (source.order + 2)
      (MvPolynomial.PartialDerivativeMachine.inputMass source.terms)) hq' hchain
  refine ⟨stages, out, steps, c, hchain, hlen, he, hspec, ?_, ?_, ?_⟩
  · intro record hm
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    simpa [mapRecord] using hwidth r hr
  · simpa [mapRecords, source, mapInput] using hcount.trans hcount'
  · have hb' := hb.trans (Nat.mul_le_mul_left 4294967296 hf)
    simpa [source, mapInput] using hb'

end ReedSolomon.HiddenDerivative.QuadraticStageRootsMachine
