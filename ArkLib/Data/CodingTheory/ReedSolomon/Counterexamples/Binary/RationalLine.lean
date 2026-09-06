/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Counterexamples.Binary.RationalLine.Errors

/-!
# Binary rational-line counterexample: definitions and complete statements

This file writes out the construction and the conclusions. The imported files supply
proofs; no problem-specific definition needs to be looked up to read the statements here.

## Field, code, and agreement

Let `F` be a field of characteristic two with `q = |F| = 2^m` elements, where `m ≥ 3`.
Set `k = q/4` and `A = q/2`. All coordinates are indexed by the whole field, including zero.

The Reed–Solomon code is

  C = { (P(x))_{x ∈ F} : P ∈ F[X], degree(P) < k }.

It has block length `q`, dimension `k`, and rate `1/4`. The degree of the zero polynomial
is minus infinity, so it is included in the condition `P.degree < k`.

For words `u,v : F → F`, their agreement is `|{x ∈ F : u(x) = v(x)}|`.
Their relative Hamming distance is `|{x ∈ F : u(x) ≠ v(x)}| / q`.
Distance to the code is the minimum of this distance over its codewords. Thus distance
at most `1/2` means agreement with a degree-`< k` polynomial on at least `A` coordinates.

## Explicit words and explaining polynomial

The binary trace is `Tr(x) = ∑_{i=0}^{m-1} x^(2^i)`, with values zero and one.
Choose `τ` with `Tr(τ) = 1`. The two source words are

  f(0) = 1,    f(x) = x^(A-1) for x ≠ 0;
  g(0) = τ,    g(x) = x⁻¹     for x ≠ 0.

For each challenge `z ∈ F`, put `s_z = 1` if `z = 0`, and `s_z = z⁻¹` otherwise.
The explicit explaining polynomial is

  P_z(X) = ∑_{i=0}^{m-2} s_z^(2^(i+1)-1) X^(2^i-1).

`Polynomial.C a` below denotes the constant polynomial `a`; `Polynomial.X` is the
indeterminate. `Finset.range r` is `{0,...,r-1}`. `Finset.univ.filter` selects exactly
those field elements satisfying its predicate, and `.card` counts them.

## Meaning of the conclusions

The theorem defines the whole agreement sets in its statement:

  S(z,P) = {x : P(x) = f(x) + z g(x)},
  T(P,Q) = {x : P(x) = f(x) and Q(x) = g(x)}.

It proves, for this same choice of τ and these same explicit words and polynomials:

1. `degree(P) < k` and `|S(z,P)| ≥ A` hold if and only if `P = P_z`.
   In particular P_z has degree below k and is the unique qualifying polynomial.
2. `|S(z,P_z)| = A` exactly, including the origin coordinate.
3. Every degree-`< k` polynomial has at most A agreements with the mixture.
4. Every pair of degree-`< k` polynomials has at most k+1 common source agreements.
5. Some pair has at least k common source agreements.

The common-agreement conclusion is the interval from k to k+1; equality with k+1 is
not asserted. Uniqueness concerns this affine line, not arbitrary received words.

## Correlated-agreement errors: definitions at radius 1/2

Here are the meanings of the two error quantities in the second theorem. A challenge
is uniformly distributed over F, so the probability of an event B is `|B|/q`.

For a source pair `(u,v)`, call it jointly close if there exist degree-`< k` polynomials
P,Q and a set H of at least A coordinates such that P(x)=u(x) and Q(x)=v(x) on H.
The CA bad event at z is:

  u+zv is within distance 1/2 of C, but (u,v) is not jointly close.

The CA error is the supremum, over all source pairs `(u,v)`, of this event's probability.
This is `ProximityGap.epsCa C (1/2) (1/2)` below.

The MCA bad event at z is that there exists a set H of at least A coordinates such that
some degree-`< k` polynomial agrees with u+zv on H, but at least one source word has no
degree-`< k` polynomial explanation on that same H. The MCA error is the supremum of
this event's probability over all source pairs. The affine-line generator uses weights
`(1,z)`; this is `mcaError (AffineLineGenerator F) C (1/2)` below.

For our constructed pair every challenge is bad: its mixture has A agreements, whereas
joint source agreement is at most k+1 < A. Hence both errors equal one. The numeric
theorem uses ArkLib's canonical code and error objects with precisely these meanings.
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
