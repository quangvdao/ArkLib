/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Counterexamples.Binary.RationalLine.Lacunary
import ArkLib.Data.CodingTheory.ReedSolomon.Counterexamples.Binary.TraceLine

/-!
# Rigidity of half-agreement explanations on the rational line

A qualifying message produces a lacunary polynomial. Its factorization determines it
uniquely, including the separate origin argument when the challenge is zero.
-/

namespace ReedSolomon.Binary

open Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

private structure RationalLineParameters (F : Type) [Fintype F] (m : ℕ) : Prop where
  card_eq : Fintype.card F = 2 * binaryTraceTopDegree m
  top_ge_four : 4 ≤ binaryTraceTopDegree m
  top_even : Even (binaryTraceTopDegree m)
  two_mul_quarter : 2 * binaryTraceQuarterDegree m = binaryTraceTopDegree m

omit [Field F] [DecidableEq F] [CharP F 2] in
private theorem rationalLine_parameters {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    RationalLineParameters F m := by
  have hT : binaryTraceTopDegree m = 2 * binaryTraceQuarterDegree m := by
    unfold binaryTraceTopDegree binaryTraceQuarterDegree
    rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
    omega
  have hq : Fintype.card F = 2 * binaryTraceTopDegree m := by
    calc
      Fintype.card F = 2 ^ ((m - 1) + 1) := by rw [hcard]; congr 1; omega
      _ = 2 * binaryTraceTopDegree m := by rw [pow_succ]; simp [binaryTraceTopDegree, mul_comm]
  have hJ : 2 ≤ binaryTraceQuarterDegree m := by
    exact Nat.le_trans (by norm_num : 2 ≤ 2 ^ 1)
      (Nat.pow_le_pow_right (by omega) (by omega))
  refine ⟨hq, ?_, ?_, hT.symm⟩
  · omega
  · exact ⟨binaryTraceQuarterDegree m, by omega⟩

/-- Half agreement determines the explaining polynomial uniquely, including the zero polynomial. -/
theorem rationalLine_polynomial_unique {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) (τ z : F) (P Q : F[X])
    (hP : P.degree < binaryTraceQuarterDegree m)
    (hQ : Q.degree < binaryTraceQuarterDegree m)
    (haP : binaryTraceTopDegree m ≤ Code.agree
      (fun x ↦ rationalPowerWord m x + z * reciprocalWord τ x) (fun x ↦ P.eval x))
    (haQ : binaryTraceTopDegree m ≤ Code.agree
      (fun x ↦ rationalPowerWord m x + z * reciprocalWord τ x) (fun x ↦ Q.eval x)) :
    P = Q := by
  classical
  have params := rationalLine_parameters hm hcard
  have hnat (R : F[X]) (hR : R.degree < binaryTraceQuarterDegree m) :
      R.natDegree < binaryTraceQuarterDegree m := by
    by_cases hr : R = 0
    · subst R
      simp only [natDegree_zero, binaryTraceQuarterDegree]
      exact pow_pos Nat.zero_lt_two _
    · exact (natDegree_lt_iff_degree_lt hr).mpr hR
  have hf (x : F) (hx : x ≠ 0) :
      x * rationalPowerWord m x = x ^ binaryTraceTopDegree m := by
    simp only [rationalPowerWord, if_neg hx]
    exact mul_pow_sub_one (by
      simp only [binaryTraceTopDegree]
      exact pow_ne_zero _ (by decide)) x
  have hg (x : F) (hx : x ≠ 0) : x * reciprocalWord τ x = 1 := by
    simp [reciprocalWord, hx]
  exact eq_of_binaryLacunary_agreement
    (binaryTraceTopDegree m) (binaryTraceQuarterDegree m) params.card_eq params.top_ge_four
    params.top_even params.two_mul_quarter.le
    (rationalPowerWord m) (reciprocalWord τ) (by simp [rationalPowerWord]) hf hg
    z P Q (hnat P hP) (hnat Q hQ)
    (polynomialAgreementSet (Function.Embedding.refl F)
      (fun x ↦ rationalPowerWord m x + z * reciprocalWord τ x) P)
    (polynomialAgreementSet (Function.Embedding.refl F)
      (fun x ↦ rationalPowerWord m x + z * reciprocalWord τ x) Q)
    (by simpa using haP) (by simpa using haQ)
    (fun _ hx ↦ (Finset.mem_filter.mp hx).2) (fun _ hx ↦ (Finset.mem_filter.mp hx).2)

end ReedSolomon.Binary
