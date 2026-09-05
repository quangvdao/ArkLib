/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.CoordinateSeparateSampleRefinement
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSampleExecution

/-!
# Initial-input coordinate decoder budget

Actual coefficient preparation, stage recovery, canonical guards, base descent, and collection
compose under one fixed numerical budget. The raw residual and guard grids remain distinct.
The output is the source collector's exact ordered result for the actual generated stage records.
-/

namespace ReedSolomon.ListDecoding.QuadraticSeparateSampleDecoder

open QuadraticAlgebra
open HiddenDerivative
local notation "qencode" => MvPolynomial.QuadraticEvaluationMachine.encode
open QuadraticPreparedDecoderMachine (Input Configuration Term decodeInput)

variable {F : Type*} [Field F] [DecidableEq F]

/-- Initial data determine a fixed host-fuel budget, independent of visited records or output. -/
def inputBudget (a : F) (input : Input F) (guards : List (F × F)) (ts : List (Term F))
    (Δ : ℕ) : ℕ :=
  17179869184 * (SeparateSampleDecoder.fuel (decodeInput a input)
    (guards.map (ArithmeticMachine.decode a)) ts Δ +
    SeparateSampleDecoder.workBound (decodeInput a input)
      (guards.map (ArithmeticMachine.decode a)) ts Δ)

/-- The closed coordinate interpreter reaches the exact source result at an initial-input budget.
All algebraic hypotheses concern the input equation and recovery samples, not desired outputs. -/
theorem execution_input_budget (a : F) (ha : ¬IsSquare a) (input : Input F)
    (guards : List (F × F)) (ts : List (Term F)) (Δ : ℕ)
    (points : Fin input.residualLength ↪ QuadraticAlgebra F a 0) :
    letI := fieldOfNonsquare a ha
    let source := decodeInput a input
    ∀ Q : DifferentialPolynomial (QuadraticAlgebra F a 0) input.order,
      source.samples = List.ofFn (fun i ↦ points i) → 0 < input.alphabet.length →
      input.order ≤ input.degree →
      MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (input.order + 2))
        (SeparateSampleDecoder.initialRootInput source ts).terms →
      MvPolynomial.EvaluationMachine.sparsePolynomial
        (SeparateSampleDecoder.initialRootInput source ts).terms =
        MvPolynomial.rename HighestJetTransport.encodeJet Q → Q ≠ 0 →
      (∀ j, jetDegree Q j < ringChar (QuadraticAlgebra F a 0)) → jetTotalDegree Q ≤ Δ →
      differentialWeightedDegree input.degree Q < input.residualLength →
      ∃ steps c out, steps + c ≤ inputBudget a input guards ts Δ ∧
        Trace a input guards steps (.start ts) c (.done (some out)) ∧
        runFuel a input guards (inputBudget a input guards ts Δ) (.start ts) =
          (.done (some out), c) ∧
        ∃ stages records,
          SeparantChainRefinement.OrderedChain
            (SeparateSampleDecoder.initialRootInput source ts).terms
            Q stages ∧
          StageRootsMachine.Specification (SeparateSampleDecoder.initialRootInput source ts)
            input.degree input.residualLength source.samples stages [] records ∧
          out = CanonicalOutputMachine.result input.order (guards.map (ArithmeticMachine.decode a))
            (input.degree + 1) input.dimension input.agreement input.received records := by
  let := fieldOfNonsquare a ha
  let source := decodeInput a input
  dsimp only
  intro Q hs hq hd hl hQ hn hc hdeg hw
  have hq' : 0 < source.alphabet.length := by simpa [source, decodeInput] using hq
  obtain ⟨sn, sc, out, hsn, ht, _hr, hsc, stages, records, hchain, hspec, hout⟩ :=
    SeparateSampleDecoder.execution_input_budget source (guards.map (ArithmeticMachine.decode a))
      ha ts Δ points hs hq' hd Q hl hQ hn hc hdeg hw
  obtain ⟨steps, c, he, hb⟩ := trace_lowering a ha source
    (guards.map (ArithmeticMachine.decode a)) ht
  have hi := QuadraticPreparedDecoderMachine.encode_decode_input a input
  change QuadraticPreparedDecoderMachine.encodeInput source = input at hi
  rw [hi] at he
  have hg : (guards.map (ArithmeticMachine.decode a)).map qencode = guards := by
    simp [List.map_map, Function.comp_def,
    MvPolynomial.QuadraticEvaluationMachine.encode, ArithmeticMachine.decode]
  rw [hg] at he
  have hbound : steps + c ≤ inputBudget a input guards ts Δ := by
    dsimp only [inputBudget]
    dsimp only [source] at hsn hsc hb
    omega
  have hsteps : steps ≤ inputBudget a input guards ts Δ := by omega
  have hr := he.runFuel_done (inputBudget a input guards ts Δ - steps)
  rw [Nat.add_sub_of_le hsteps] at hr
  exact ⟨steps, c, out, hbound, he, hr, stages, records, hchain, hspec, hout⟩

end ReedSolomon.ListDecoding.QuadraticSeparateSampleDecoder
