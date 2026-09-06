/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Counterexamples.Binary.RationalLine.Bounds
import ArkLib.Data.CodingTheory.ReedSolomon.Counterexamples.Binary.RationalLine.Rigidity
import ArkLib.Data.CodingTheory.ReedSolomon.Agreement.Interpolation

/-!
# A rational affine line with unique half-agreement explanations

Let `F` have size `q = 2 ^ m`, with `m ≥ 3`. Put `k = q / 4` and `A = q / 2`.
Choose `τ` of binary trace one and define

* `f(0) = 1`, with `f(x) = x ^ (q / 2 - 1)` off zero;
* `g(0) = τ`, with `g(x) = x⁻¹` off zero.

For every `z`, the degree-`< k` polynomials agreeing with `f + z g` on at least `A`
coordinates form exactly the singleton containing `rationalLinePolynomial m z`.
This explicit polynomial agrees on exactly `A` coordinates. Common source agreement
of two degree-`< k` polynomials lies between `k` and `k + 1`, in the sense of a universal
upper bound and an attained lower bound. The evaluation domain is the whole field.

`RationalLineBounds` collects these conclusions for the same words and explanations.
`rationalLine_bounds` verifies the explicit construction for any trace-one `τ`;
`exists_rationalLine` supplies such a `τ`. This is uniqueness on the constructed line,
not a global unique-decoding assertion. The CA and MCA error-one consequences are in
`RationalLine/Errors.lean`.

The proof separates explicit trace witnesses, rigidity of a single qualifying polynomial,
and the reciprocal/interpolation bounds for common source agreement.
-/

namespace ReedSolomon.Binary

open Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The explicit rational line has exact singleton half-agreement lists and common source
agreement between one quarter of the field and one quarter plus one. -/
theorem rationalLine_bounds {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) {τ : F} (hτ : binaryTrace m τ = 1) :
    RationalLineBounds (Fintype.card F / 4) (Fintype.card F / 2)
      (rationalPowerWord m) (reciprocalWord τ) (rationalLinePolynomial m) := by
  have hquarter := binaryTraceQuarterDegree_eq_card_div_four (F := F) (by omega) hcard
  have hhalf := binaryTraceTopDegree_eq_card_div_two (F := F) (by omega) hcard
  rw [← hquarter, ← hhalf]
  refine ⟨?_, rationalLinePolynomial_agree_eq hm hcard hτ, ?_, ?_⟩
  · intro z P
    constructor
    · rintro ⟨hP, ha⟩
      exact rationalLine_polynomial_unique hm hcard τ z P (rationalLinePolynomial m z) hP
        (rationalLinePolynomial_degree_lt hm z) ha
        (rationalLinePolynomial_agree_eq hm hcard hτ z).ge
    · rintro rfl
      exact ⟨rationalLinePolynomial_degree_lt hm z,
        (rationalLinePolynomial_agree_eq hm hcard hτ z).ge⟩
  · intro P Q _hP hQ
    exact commonPolynomialAgreementSet_reciprocalWord_card_le _ τ P Q _ hQ
  · apply exists_commonPolynomialAgreementSet_card_ge
    rw [hquarter]
    exact Nat.div_le_self _ _

/-- Every binary field of size at least eight admits the explicit rational-line construction.
The dimension and agreement threshold are visibly one quarter and one half of the field size. -/
theorem exists_rationalLine {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    let q := Fintype.card F
    ∃ τ : F, binaryTrace m τ = 1 ∧
      RationalLineBounds (q / 4) (q / 2)
        (rationalPowerWord m) (reciprocalWord τ) (rationalLinePolynomial m) := by
  obtain ⟨τ, hτ⟩ := exists_binaryTrace_eq_one (F := F) (by omega : 0 < m) hcard
  exact ⟨τ, hτ, rationalLine_bounds hm hcard hτ⟩

end ReedSolomon.Binary
