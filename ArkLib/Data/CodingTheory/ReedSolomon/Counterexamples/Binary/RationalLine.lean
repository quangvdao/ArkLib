/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.BinaryLacunaryAgreement
import ArkLib.Data.CodingTheory.ReedSolomon.Counterexamples.Binary.TraceLine
import ArkLib.Data.CodingTheory.ReedSolomon.ReciprocalWord
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.LowerBound

/-!
# A rational affine line with half agreement over binary fields

For a field of size `q = 2 ^ m`, with `m ≥ 3`, put `T = q / 2` and `J = q / 4`.
Choose `τ` of binary trace one. The two words are

* `f(0) = 1` and `f(x) = x ^ (T - 1)` for `x ≠ 0`;
* `g(0) = τ` and `g(x) = x⁻¹` for `x ≠ 0`.

Every word `f + z g` has exactly one polynomial of degree less than `J` agreeing on at
least `T` coordinates; that polynomial agrees on exactly `T` coordinates. In contrast,
a pair of degree-less-than-`J` polynomials can simultaneously explain `f` and `g` on
at most `J + 1 < T` coordinates. Interpolation supplies a common explanation on `J`
coordinates. The statements concern the full evaluation domain, including zero.

The witnesses are explicit quotients of normalized binary trace polynomials. Uniqueness
comes from the rigidity of lacunary polynomials with at least `T - 1` roots, with a separate
argument at `z = 0` to account for the prescribed origin value.
-/

namespace ReedSolomon.Binary

open Polynomial CoreDefinitions
open scoped NNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

omit [Field F] [DecidableEq F] [CharP F 2] in
private theorem rationalLine_parameters {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    Fintype.card F = 2 * binaryTraceTopDegree m ∧
    4 ≤ binaryTraceTopDegree m ∧ Even (binaryTraceTopDegree m) ∧
    2 * binaryTraceQuarterDegree m = binaryTraceTopDegree m ∧
    binaryTraceQuarterDegree m + 1 < binaryTraceTopDegree m ∧
    binaryTraceQuarterDegree m ≤ Fintype.card F := by
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
  refine ⟨hq, ?_, ?_, hT.symm, ?_, ?_⟩
  · omega
  · exact ⟨binaryTraceQuarterDegree m, by omega⟩
  · omega
  · omega

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
  obtain ⟨hc, hT, hTeven, hJT, _, _⟩ := rationalLine_parameters hm hcard
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
    rw [← pow_succ']
    congr 1
    omega
  have hg (x : F) (hx : x ≠ 0) : x * reciprocalWord τ x = 1 := by
    simp [reciprocalWord, hx]
  exact eq_of_binaryLacunary_agreement
    (binaryTraceTopDegree m) (binaryTraceQuarterDegree m) hc hT hTeven hJT.le
    (rationalPowerWord m) (reciprocalWord τ) (by simp [rationalPowerWord]) hf hg
    z P Q (hnat P hP) (hnat Q hQ)
    (Finset.univ.filter fun x ↦ rationalPowerWord m x + z * reciprocalWord τ x = P.eval x)
    (Finset.univ.filter fun x ↦ rationalPowerWord m x + z * reciprocalWord τ x = Q.eval x)
    haP haQ (fun _ hx ↦ (Finset.mem_filter.mp hx).2.symm)
    (fun _ hx ↦ (Finset.mem_filter.mp hx).2.symm)

/-- Every mixture has exactly one message polynomial with at least half agreement. -/
theorem rationalLine_existsUnique {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) {τ : F} (hτ : binaryTrace m τ = 1) (z : F) :
    ∃! P : F[X], P.degree < binaryTraceQuarterDegree m ∧
      binaryTraceTopDegree m ≤ Code.agree
        (fun x ↦ rationalPowerWord m x + z * reciprocalWord τ x) (fun x ↦ P.eval x) := by
  obtain ⟨P, hp, ha⟩ := rationalLine_agreement_witness hm hcard hτ z
  have hdegree : P.degree < binaryTraceQuarterDegree m :=
    degree_le_natDegree.trans_lt (by exact_mod_cast hp)
  refine ⟨P, ⟨hdegree, ha.ge⟩, ?_⟩
  intro Q hQ
  exact rationalLine_polynomial_unique hm hcard τ z Q P hQ.1 hdegree hQ.2 ha.ge

/-- Half the field is the maximum agreement attained by any message polynomial on the line. -/
theorem rationalLine_agree_le {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) {τ : F} (hτ : binaryTrace m τ = 1)
    (z : F) (P : F[X]) (hp : P.degree < binaryTraceQuarterDegree m) :
    Code.agree (fun x ↦ rationalPowerWord m x + z * reciprocalWord τ x)
      (fun x ↦ P.eval x) ≤ binaryTraceTopDegree m := by
  obtain ⟨Q, hq, ha⟩ := rationalLine_agreement_witness hm hcard hτ z
  by_cases hlarge : binaryTraceTopDegree m ≤ Code.agree
      (fun x ↦ rationalPowerWord m x + z * reciprocalWord τ x) (fun x ↦ P.eval x)
  · have heq := rationalLine_polynomial_unique hm hcard τ z P Q hp
      (degree_le_natDegree.trans_lt (by exact_mod_cast hq)) hlarge ha.ge
    simpa only [heq, ha] using (le_refl (binaryTraceTopDegree m))
  · exact (lt_of_not_ge hlarge).le

/-- The unique half-agreement explanation attains exactly half agreement. -/
theorem rationalLine_existsUnique_exact {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) {τ : F} (hτ : binaryTrace m τ = 1) (z : F) :
    ∃! P : F[X], P.degree < binaryTraceQuarterDegree m ∧
      Code.agree (fun x ↦ rationalPowerWord m x + z * reciprocalWord τ x)
        (fun x ↦ P.eval x) = binaryTraceTopDegree m := by
  obtain ⟨P, hp, hunique⟩ := rationalLine_existsUnique hm hcard hτ z
  refine ⟨P, ⟨hp.1, le_antisymm (rationalLine_agree_le hm hcard hτ z P hp.1) hp.2⟩, ?_⟩
  intro Q hQ
  exact hunique Q ⟨hQ.1, hQ.2.ge⟩

omit [CharP F 2] in
/-- Every pair of message polynomials has common source agreement at most `q / 4 + 1`. -/
theorem rationalLine_commonAgreement_le {m : ℕ} (τ : F) (P Q : F[X])
    (hQ : Q.degree < binaryTraceQuarterDegree m) :
    (commonPolynomialAgreementSet (Function.Embedding.refl F)
      (rationalPowerWord m) (reciprocalWord τ) P Q).card ≤
      binaryTraceQuarterDegree m + 1 :=
  commonPolynomialAgreementSet_reciprocalWord_card_le _ τ P Q _ hQ

omit [CharP F 2] in
/-- Interpolation attains common source agreement at least `q / 4`. -/
theorem rationalLine_commonAgreement_ge {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) (τ : F) :
    ∃ P Q : F[X], P.degree < binaryTraceQuarterDegree m ∧
      Q.degree < binaryTraceQuarterDegree m ∧
      binaryTraceQuarterDegree m ≤
        (commonPolynomialAgreementSet (Function.Embedding.refl F)
          (rationalPowerWord m) (reciprocalWord τ) P Q).card :=
  exists_commonPolynomialAgreementSet_card_ge _ _ _ _
    (rationalLine_parameters hm hcard).2.2.2.2.2

omit [DecidableEq F] in
/-- The quarter-rate full-domain RS code has affine-line MCA error one at half distance. -/
theorem rationalLine_mcaError_eq_one {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    mcaError (AffineLineGenerator F)
      (code (Function.Embedding.refl F) (binaryTraceQuarterDegree m)) (1 / 2) = 1 := by
  classical
  obtain ⟨τ, hτ⟩ := exists_binaryTrace_eq_one (F := F) (by omega : 0 < m) hcard
  obtain ⟨hc, _, _, _, hgap, _⟩ := rationalLine_parameters hm hcard
  apply mcaError_affineLine_eq_one_of_agreement_witnesses
    (Function.Embedding.refl F) (binaryTraceQuarterDegree m) (binaryTraceTopDegree m)
    (1 / 2) (rationalPowerWord m) (reciprocalWord τ)
  · rw [hc]
    push_cast
    linarith
  · intro z
    obtain ⟨P, hp, ha⟩ := rationalLine_agreement_witness hm hcard hτ z
    exact ⟨P, degree_le_natDegree.trans_lt (by exact_mod_cast hp), ha.ge⟩
  · intro P hp
    exact (agree_reciprocalWord_le τ P _ hp).trans_lt hgap

/-- The same code has ordinary correlated-agreement error one at half distance. -/
theorem rationalLine_epsCa_eq_one {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    ProximityGap.epsCa (F := F)
      (code (Function.Embedding.refl F) (binaryTraceQuarterDegree m) : Set (F → F))
      (1 / 2 : ℝ≥0) (1 / 2 : ℝ≥0) = 1 := by
  obtain ⟨τ, hτ⟩ := exists_binaryTrace_eq_one (F := F) (by omega : 0 < m) hcard
  obtain ⟨hc, _, _, _, hgap, _⟩ := rationalLine_parameters hm hcard
  apply epsCa_half_eq_one_of_agreement_witnesses
    (Function.Embedding.refl F) (binaryTraceQuarterDegree m) (binaryTraceTopDegree m)
    hc (rationalPowerWord m) (reciprocalWord τ)
  · intro z
    obtain ⟨P, hp, ha⟩ := rationalLine_agreement_witness hm hcard hτ z
    exact ⟨P, degree_le_natDegree.trans_lt (by exact_mod_cast hp), ha.ge⟩
  · intro P hp
    exact (agree_reciprocalWord_le τ P _ hp).trans_lt hgap

end ReedSolomon.Binary
