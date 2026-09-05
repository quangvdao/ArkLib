/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.PreparedInterpolationProof
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.OrderZeroDecoderCertificate
import ArkLib.Data.QuadraticAlgebra.SetupRefinement

/-!
# Exact quarter-gap decoding through the actual quadratic setup

The setup parameter, alphabet and samples are the outputs of the executed setup machine.
The interpolant likewise comes from the direct order-zero attempt, including ambient degree zero.
The existing prepared pipeline then produces exactly the agreeing polynomials. The three child
executions are certified separately; no whole-driver runtime or cost bound is asserted here.
The sample-capacity premise is explicit, and this branch requires at least three coordinates.
-/

namespace ReedSolomon.ListDecoding.OrderZeroPreparedDecoderProof

open Polynomial JetHornerMachine HiddenDerivative

/-- Actual setup and direct interpolation feed an exact prepared execution for quarter gaps. -/
theorem quarter_run_exact {q n k A : ℕ} [Fact q.Prime]
    (delta : ℝ) (hdelta : (1 / 4 : ℝ) ≤ delta)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (hn : 3 ≤ n) (hk : 0 < k) (hkn : k ≤ n) (hnq : n ≤ q)
    (hA : AllRateListDecoding.agreementThreshold delta n k ≤ A)
    (hL : (n / 2) * A ≤ q ^ 2) :
    let L := (n / 2) * A
    ∃ (a : ZMod q) (data : QuadraticAlgebra.SetupMachine.Prepared q a)
      (setupCost : QuadraticAlgebra.SetupMachine.Cost)
      (hc : QuadraticAlgebra.SetupMachine.Correct L a data)
      (interpolant : NonzeroInterpolationMachine.Output (ZMod q)) (ic : ℕ),
      QuadraticAlgebra.SetupMachine.runFuel L (QuadraticAlgebra.SetupMachine.budget q L)
        (.base .start) = (.done (some ⟨a, data⟩), setupCost) ∧
      setupCost.total ≤ QuadraticAlgebra.SetupMachine.budget q L ∧
      NonzeroInterpolationMachine.run (k - 1) 0 (n / 2) A
        (List.ofFn fun i ↦ (domain i, received i)) = (some interpolant, ic) ∧
      NonzeroInterpolationMachine.Certified (d := 0) (k - 1) (n / 2) A
        (List.ofFn fun i ↦ (domain i, received i)) interpolant ∧
      ic ≤ NonzeroInterpolationMachine.zeroAttemptBudget (n / 2) A n ∧
      let input : PreparedDecoderMachine.Input (ZMod q) a :=
        ⟨data.alphabet, data.samples, List.ofFn (fun i ↦ (domain i, received i)),
          0, k - 1, L, k, A⟩
    ∃ steps cost out,
      PreparedDecoderMachine.Trace input hc.nonsquare steps (.start interpolant.terms) cost
        (.done (some out)) ∧
      PreparedDecoderMachine.runFuel input hc.nonsquare steps (.start interpolant.terms) =
        (.done (some out), cost) ∧
      (out.map coefficientPolynomial).Nodup ∧ out.Nodup ∧
      (∀ f : (ZMod q)[X], f ∈ out.map coefficientPolynomial ↔
        f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received) ∧
      (∀ cs : List (ZMod q), cs ∈ out ↔ cs.length = k ∧
        (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received) := by
  dsimp only
  obtain ⟨a, data, setupCost, hsetup, hc, hsetupCost⟩ :=
    QuadraticAlgebra.SetupMachine.setup_correct ((n / 2) * A)
      (Fact.out : q.Prime) (by omega) hL
  obtain ⟨interpolant, ic, hi, hcert, hic, _hne, _helig, _hjet, hweight, hchar, _hlocal⟩ :=
    OrderZeroDecoderCertificate.quarter_attempt_characteristic delta hdelta n k A hn hk hA
      (by simpa only [ringChar.eq (ZMod q) q] using hnq) domain received
  obtain ⟨points, hpoints⟩ := hc.samples_embedding
  have hbelow : IsBelowCharacteristic (k - 1)
      (NonzeroInterpolationMachine.sourceOutput (d := 0) (k - 1) (n / 2) A interpolant) := by
    refine ⟨?_, hchar⟩
    rw [ringChar.eq (ZMod q) q]
    omega
  refine ⟨a, data, setupCost, hc, interpolant, ic, hsetup, hsetupCost, hi, hcert, hic, ?_⟩
  exact PreparedInterpolationProof.run_exact domain received interpolant
    (congrArg Prod.fst hi) (Nat.zero_le _) (by omega) a hc.nonsquare data.alphabet
    data.samples points hpoints hc.extension_complete hc.extension_nodup hbelow hweight

/-- For a feasible threshold, the block and field bounds discharge sample capacity. -/
theorem quarter_run_exact_of_le_blockLength {q n k A : ℕ} [Fact q.Prime]
    (delta : ℝ) (hdelta : (1 / 4 : ℝ) ≤ delta)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (hn : 3 ≤ n) (hk : 0 < k) (hkn : k ≤ n) (hnq : n ≤ q)
    (hA : AllRateListDecoding.agreementThreshold delta n k ≤ A)
    (hAn : A ≤ n) :
    let L := (n / 2) * A
    ∃ (a : ZMod q) (data : QuadraticAlgebra.SetupMachine.Prepared q a)
      (setupCost : QuadraticAlgebra.SetupMachine.Cost)
      (hc : QuadraticAlgebra.SetupMachine.Correct L a data)
      (interpolant : NonzeroInterpolationMachine.Output (ZMod q)) (ic : ℕ),
      QuadraticAlgebra.SetupMachine.runFuel L (QuadraticAlgebra.SetupMachine.budget q L)
        (.base .start) = (.done (some ⟨a, data⟩), setupCost) ∧
      setupCost.total ≤ QuadraticAlgebra.SetupMachine.budget q L ∧
      NonzeroInterpolationMachine.run (k - 1) 0 (n / 2) A
        (List.ofFn fun i ↦ (domain i, received i)) = (some interpolant, ic) ∧
      NonzeroInterpolationMachine.Certified (d := 0) (k - 1) (n / 2) A
        (List.ofFn fun i ↦ (domain i, received i)) interpolant ∧
      ic ≤ NonzeroInterpolationMachine.zeroAttemptBudget (n / 2) A n ∧
      let input : PreparedDecoderMachine.Input (ZMod q) a :=
        ⟨data.alphabet, data.samples, List.ofFn (fun i ↦ (domain i, received i)),
          0, k - 1, L, k, A⟩
    ∃ steps cost out,
      PreparedDecoderMachine.Trace input hc.nonsquare steps (.start interpolant.terms) cost
        (.done (some out)) ∧
      PreparedDecoderMachine.runFuel input hc.nonsquare steps (.start interpolant.terms) =
        (.done (some out), cost) ∧
      (out.map coefficientPolynomial).Nodup ∧ out.Nodup ∧
      (∀ f : (ZMod q)[X], f ∈ out.map coefficientPolynomial ↔
        f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received) ∧
      (∀ cs : List (ZMod q), cs ∈ out ↔ cs.length = k ∧
        (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received) := by
  have hL : (n / 2) * A ≤ q ^ 2 := by
    calc
      (n / 2) * A ≤ n * n := Nat.mul_le_mul (Nat.div_le_self n 2) hAn
      _ ≤ q * q := Nat.mul_le_mul hnq hnq
      _ = q ^ 2 := (pow_two q).symm
  exact quarter_run_exact delta hdelta domain received hn hk hkn hnq hA hL

end ReedSolomon.ListDecoding.OrderZeroPreparedDecoderProof
