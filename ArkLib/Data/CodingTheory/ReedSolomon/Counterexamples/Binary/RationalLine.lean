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

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- Complete deterministic statement, with every construction and agreement set written out. -/
theorem exists_rationalLine_explicit {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    let q := Fintype.card F
    let k := q / 4
    let A := q / 2
    let trace := fun x : F ↦ ∑ i ∈ Finset.range m, x ^ (2 ^ i)
    let f := fun x : F ↦ if x = 0 then 1 else x ^ (A - 1)
    let p := fun z : F ↦
      let s := if z = 0 then 1 else z⁻¹
      ∑ i ∈ Finset.range (m - 1), C (s ^ (2 ^ (i + 1) - 1)) * X ^ (2 ^ i - 1)
    ∃ τ : F, trace τ = 1 ∧
      let g := fun x : F ↦ if x = 0 then τ else x⁻¹
      let S := fun z (P : F[X]) ↦
        Finset.univ.filter fun x : F ↦ P.eval x = f x + z * g x
      let T := fun (P Q : F[X]) ↦
        Finset.univ.filter fun x : F ↦ P.eval x = f x ∧ Q.eval x = g x
      -- The entire qualifying list is the singleton containing the explicit p(z).
      (∀ (z : F) (P : F[X]), (P.degree < k ∧ A ≤ (S z P).card) ↔ P = p z) ∧
      -- There is no extra agreement, including at zero.
      (∀ z, (S z (p z)).card = A) ∧
      -- No other message polynomial attains greater agreement.
      (∀ (z : F) (P : F[X]), P.degree < k → (S z P).card ≤ A) ∧
      -- Common source agreement: universal upper bound and attained lower bound.
      (∀ P Q : F[X], P.degree < k → Q.degree < k → (T P Q).card ≤ k + 1) ∧
      (∃ P Q : F[X], P.degree < k ∧ Q.degree < k ∧ k ≤ (T P Q).card) := by
  classical
  obtain ⟨τ, hτ, h⟩ := exists_rationalLine (F := F) hm hcard
  refine ⟨τ, hτ, ?_⟩
  have hhalf := binaryTraceTopDegree_eq_card_div_two (F := F) (by omega) hcard
  have hparts := And.intro h.exactList (And.intro h.exactAgreement
    (And.intro h.agree_le (And.intro h.commonUpper h.commonLower)))
  simpa [rationalPowerWord, hhalf, rationalLinePolynomial, binaryTraceQuotient,
    reciprocalWord, Code.agree, commonPolynomialAgreementSet, eq_comm] using hparts

/-- Both canonical errors are exactly one for the full-domain quarter-rate code.
The code, radius, source experiments, and supremum defining these errors are written out above. -/
theorem rationalLine_error_values {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    let k := Fintype.card F / 4
    -- `code (Embedding.refl F) k` is precisely evaluations of all degree-<k polynomials on F.
    ProximityGap.epsCa (F := F)
      (code (Function.Embedding.refl F) k : Set (F → F)) (1 / 2 : ℝ≥0) (1 / 2 : ℝ≥0) = 1 ∧
    mcaError (AffineLineGenerator F) (code (Function.Embedding.refl F) k) (1 / 2) = 1 :=
  ⟨rationalLine_epsCa_eq_one hm hcard, rationalLine_mcaError_eq_one hm hcard⟩

end ReedSolomon.Binary
