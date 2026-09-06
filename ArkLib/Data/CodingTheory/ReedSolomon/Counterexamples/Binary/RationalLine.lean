/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Counterexamples.Binary.RationalLine.Errors

/-!
# Binary rational-line counterexample

This file is the reader-facing statement of the binary-field rational-line counterexample.
It writes out the field parameters, the two source words, the affine mixtures, the explicit
explaining polynomial, and the relevant agreement sets in one place. The first theorem gives
the complete deterministic construction; the second records its consequences for ArkLib's
correlated-agreement and multi-correlated-agreement errors.

The supporting modules contain the reusable definitions and proofs. Here, comments are placed
beside the corresponding Lean expressions so that the mathematical statement can be read from
top to bottom without unfolding problem-specific abbreviations or moving between files.
-/

namespace ReedSolomon.Binary

open Polynomial CoreDefinitions
open scoped NNReal

-- Work over a finite field of characteristic two; coordinates include every element of F.
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- Complete deterministic statement, with every construction and agreement set written out. -/
theorem exists_rationalLine_explicit {m : ℕ} (hm : 3 ≤ m) -- m ≥ 3, hence q ≥ 8.
    (hcard : Fintype.card F = 2 ^ m) :
    let q := Fintype.card F -- Block length: the entire field, including zero.
    let k := q / 4 -- Message polynomials have degree < k; the code has rate 1/4.
    let A := q / 2 -- Half the coordinates: the agreement threshold at distance 1/2.
    -- Tr(x) = x + x² + ⋯ + x^(2^(m-1)), with values in {0,1}.
    -- Finset.range m indexes i = 0,...,m-1.
    let trace := fun x : F ↦ ∑ i ∈ Finset.range m, x ^ (2 ^ i)
    -- First source word: f(0) = 1, and f(x) = x^(q/2-1) away from zero.
    let f := fun x : F ↦ if x = 0 then 1 else x ^ (A - 1)
    -- For each challenge z, this is the explicit explaining polynomial P_z(X).
    let p := fun z : F ↦
      let s := if z = 0 then 1 else z⁻¹
      -- Sum over i = 0,...,m-2; C embeds a coefficient into F[X], and X is the indeterminate.
      ∑ i ∈ Finset.range (m - 1), C (s ^ (2 ^ (i + 1) - 1)) * X ^ (2 ^ i - 1)
    -- One trace-one value τ works for all challenges and all conclusions below.
    ∃ τ : F, trace τ = 1 ∧
      -- Second source word: g(0) = τ, and g(x) = 1/x away from zero.
      let g := fun x : F ↦ if x = 0 then τ else x⁻¹
      -- S(z,P) = {x ∈ F : P(x) = f(x) + z g(x)}: mixture agreement coordinates.
      -- univ.filter selects these coordinates; .card below is their number.
      let S := fun z (P : F[X]) ↦
        Finset.univ.filter fun x : F ↦ P.eval x = f x + z * g x
      -- T(P,Q) = {x ∈ F : P(x) = f(x) AND Q(x) = g(x)}: common source agreement.
      let T := fun (P Q : F[X]) ↦
        Finset.univ.filter fun x : F ↦ P.eval x = f x ∧ Q.eval x = g x
      -- Exact list: a degree-<k polynomial agrees on ≥ q/2 coordinates iff it is P_z.
      -- This also proves degree(P_z) < k. The zero polynomial has degree -∞ in Lean.
      -- Uniqueness is asserted on this constructed line, not for arbitrary received words.
      (∀ (z : F) (P : F[X]), (P.degree < k ∧ A ≤ (S z P).card) ↔ P = p z) ∧
      -- P_z agrees on exactly q/2 coordinates, counting zero as an ordinary coordinate.
      (∀ z, (S z (p z)).card = A) ∧
      -- Every codeword has ≤ q/2 agreements: each mixture has distance exactly 1/2 to the code.
      (∀ (z : F) (P : F[X]), P.degree < k → (S z P).card ≤ A) ∧
      -- Any two message polynomials simultaneously explain at most q/4 + 1 source coordinates.
      (∀ P Q : F[X], P.degree < k → Q.degree < k → (T P Q).card ≤ k + 1) ∧
      -- Some pair explains at least q/4 coordinates. Thus the maximum lies in [k,k+1];
      -- equality with k+1 is not asserted. Since q ≥ 8, k+1 < A: joint half-agreement fails.
      (∃ P Q : F[X], P.degree < k ∧ Q.degree < k ∧ k ≤ (T P Q).card) := by
  classical
  -- Use the proved construction, then unfold its packaged conclusions into the statement above.
  obtain ⟨τ, hτ, h⟩ := exists_rationalLine (F := F) hm hcard
  refine ⟨τ, hτ, ?_⟩
  have hhalf := binaryTraceTopDegree_eq_card_div_two (F := F) (by omega) hcard
  have hparts := And.intro h.exactList (And.intro h.exactAgreement
    (And.intro h.agree_le (And.intro h.commonUpper h.commonLower)))
  simpa [rationalPowerWord, hhalf, rationalLinePolynomial, binaryTraceQuotient,
    reciprocalWord, Code.agree, commonPolynomialAgreementSet, eq_comm] using hparts

/-- Both correlated-agreement errors equal one for the full-domain quarter-rate code. -/
theorem rationalLine_error_values {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    let k := Fintype.card F / 4
    -- The code below is C = { (P(x))_{x∈F} : degree(P) < k }; Embedding.refl uses all of F.
    -- Distance is |{x : u(x) ≠ v(x)}|/q, minimized over codewords for distance to C.
    -- CA error = sup over source pairs (u,v) of the probability, for uniform z ∈ F, that:
    --   (i) u+zv is within distance 1/2 of C, and
    --   (ii) no degree-<k pair P,Q agrees with u,v on a common set of ≥ q/2 coordinates.
    -- Each event has probability |{bad z}|/q. The two radii below are both 1/2.
    -- Our constructed pair makes every z bad, so this supremum is exactly 1.
    ProximityGap.epsCa (F := F)
      (code (Function.Embedding.refl F) k : Set (F → F)) (1 / 2 : ℝ≥0) (1 / 2 : ℝ≥0) = 1 ∧
    -- MCA error = sup over (u,v) of the probability that there exists H, |H| ≥ q/2,
    -- on which u+zv has a degree-<k explanation but at least one of u,v has none on H.
    -- AffineLineGenerator supplies weights (1,z), with z uniform in F.
    -- Take H = S(z,P_z): a simultaneous source explanation would contradict |T| ≤ k+1 < q/2.
    mcaError (AffineLineGenerator F) (code (Function.Embedding.refl F) k) (1 / 2) = 1 :=
  ⟨rationalLine_epsCa_eq_one hm hcard, rationalLine_mcaError_eq_one hm hcard⟩

end ReedSolomon.Binary
