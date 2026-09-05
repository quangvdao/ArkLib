/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.Extension
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.RecursiveCounting
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.RegularCounting


/-!
# Polynomial bounds for differential roots

This file assembles singular recursion, regular-jet counting, and finite-extension descent into
the quantitative differential root bound used by hidden-derivative Reed--Solomon decoding.

The final count uses the fixed cubic extension of the coefficient field.  Its exponent is
therefore independent of the weighted-degree budget.  Both the ambient polynomial degree and
every individual jet degree remain strictly below the characteristic; extending the field
increases its cardinality without changing that characteristic.
-/

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F E : Type*} {d D : ℕ}

/-! ### Degree transport -/

/-- An injective coefficient map preserves the root-specialization weighted degree exactly. -/
theorem differentialWeightedDegree_map_eq [CommSemiring F] [CommSemiring E]
    (f : F →+* E) (hf : Function.Injective f) (Q : DifferentialPolynomial F d) :
    differentialWeightedDegree D (MvPolynomial.map f Q) =
      differentialWeightedDegree D Q := by
  unfold differentialWeightedDegree MvPolynomial.weightedTotalDegree
  rw [MvPolynomial.support_map_of_injective Q hf]

/-! ### Natural-number cancellation -/

/-- If twice the exceptional-point budget fits in the witness field, truncated subtraction
retains at least half of the field. -/
private theorem card_le_two_mul_card_sub {S H : ℕ} (hlarge : 2 * H ≤ S) :
    S ≤ 2 * (S - H) := by
  omega

/-- Cancel a positive witness-field factor after replacing `S - H` by half of `S`. -/
private theorem card_le_two_mul_of_sub_mul_le {S H roots budget : ℕ}
    (hS : 0 < S) (hlarge : 2 * H ≤ S)
    (hcount : (S - H) * roots ≤ S * budget) :
    roots ≤ 2 * budget := by
  apply Nat.le_of_mul_le_mul_left ?_ hS
  calc
    S * roots ≤ (2 * (S - H)) * roots :=
      Nat.mul_le_mul_right roots (card_le_two_mul_card_sub hlarge)
    _ = 2 * ((S - H) * roots) := by ring
    _ ≤ 2 * (S * budget) := Nat.mul_le_mul_left 2 hcount
    _ = S * (2 * budget) := by ring

/-! ### Fixed-extension root count -/

/-- Division-free root count after passing to the fixed cubic extension.

The factor `|F| ^ 3 - H` is retained exactly.  This statement exposes the regular-witness
arithmetic before the final half-field cancellation, and does not require `H` to be smaller than
the extension field. -/
theorem boundedSolution_cubicExtension_sub_mul_le [Field F] [Finite F]
    (Q : DifferentialPolynomial F d) (H Δ : ℕ)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q ≤ H)
    (hDegree : ∀ s, jetDegree Q s ≤ Δ) :
    (Nat.card F ^ 3 - H) * Nat.card (BoundedSolution Q D) ≤
      ((d + 1) * Δ) * (Nat.card F ^ 3 * Δ * (Nat.card F ^ 3) ^ d) := by
  let _ : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  let E := FiniteField.Extension F (ringChar F) 3
  let Qₑ : DifferentialPolynomial E d := MvPolynomial.map (algebraMap F E) Q
  let _ := Fintype.ofFinite E
  let _ := Fintype.ofFinite (BoundedSolution Qₑ D)
  let roots : Finset (BoundedSolution Qₑ D) := Finset.univ
  have hcardE : Nat.card E = Nat.card F ^ 3 := by
    change Nat.card (FiniteField.Extension F (ringChar F) 3) = Nat.card F ^ 3
    exact FiniteField.natCard_extension F (ringChar F) 3
  have hQₑ : Qₑ ≠ 0 := by
    intro hzero
    apply hQ
    apply MvPolynomial.map_injective (algebraMap F E) (algebraMap F E).injective
    simpa [Qₑ] using hzero
  have hcharₑ : IsBelowCharacteristic D Qₑ := by
    exact (isBelowCharacteristic_map_iff Q D).mpr hchar
  have hWeightₑ : differentialWeightedDegree D Qₑ ≤ H := by
    change differentialWeightedDegree D (MvPolynomial.map (algebraMap F E) Q) ≤ H
    rw [differentialWeightedDegree_map_eq
      (algebraMap F E) (algebraMap F E).injective Q]
    exact hWeight
  have hDegreeₑ : ∀ s, jetDegree Qₑ s ≤ Δ := by
    intro s
    change jetDegree (MvPolynomial.map (algebraMap F E) Q) s ≤ Δ
    rw [jetDegree_map_eq (algebraMap F E) (algebraMap F E).injective Q s]
    exact hDegree s
  have hRegular : RegularBranchBudget Qₑ D (Nat.card E - H)
      (Nat.card E * Δ * Nat.card E ^ d) := by
    intro current s hreach hactive hcurrent regular hregular
    apply regularBranch_counting_pow_le current s H Δ
    · exact isHighestActiveJet_of_highestActiveJet_eq_some hactive
    · exact hcurrent.1
    · exact (differentialWeightedDegree_le_of_reflTransGen_singularStep hreach).trans hWeightₑ
    · exact (jetDegree_le_of_reflTransGen_singularStep hreach s).trans (hDegreeₑ s)
    · exact hregular
  have hExtension := boundedSolution_recursive_counting_of_jetDegree_le
    Qₑ hQₑ hcharₑ (Nat.card E - H) (Nat.card E * Δ * Nat.card E ^ d) Δ roots
    hDegreeₑ hRegular
  have hDescent : Nat.card (BoundedSolution Q D) ≤ Nat.card (BoundedSolution Qₑ D) := by
    exact BoundedSolution.natCard_le_extension Q D
  calc
    (Nat.card F ^ 3 - H) * Nat.card (BoundedSolution Q D)
        ≤ (Nat.card F ^ 3 - H) * Nat.card (BoundedSolution Qₑ D) :=
      Nat.mul_le_mul_left _ hDescent
    _ = (Nat.card E - H) * roots.card := by
      rw [hcardE]
      simp only [roots, Finset.card_univ, Nat.card_eq_fintype_card]
    _ ≤ ((d + 1) * Δ) * (Nat.card E * Δ * Nat.card E ^ d) := hExtension
    _ = ((d + 1) * Δ) *
        (Nat.card F ^ 3 * Δ * (Nat.card F ^ 3) ^ d) := by
      rw [hcardE]

/-- Polynomial-in-`|F|` root count with a fixed exponent depending only on the derivative order.

The hypotheses make the characteristic boundary explicit: both the ambient degree `D` and every
individual jet degree are strictly below `ringChar F` through `IsBelowCharacteristic`.  The cubic
extension supplies enough witness points whenever the weighted-degree budget is at most `|F|²`.
-/
theorem natCard_boundedSolution_le_two_mul_pow [Field F] [Finite F]
    (Q : DifferentialPolynomial F d) (Δ : ℕ)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q ≤ Nat.card F ^ 2)
    (hDegree : ∀ s, jetDegree Q s ≤ Δ)
    (hDelta : Δ ≤ Nat.card F) :
    Nat.card (BoundedSolution Q D) ≤
      2 * (d + 1) * Nat.card F ^ (3 * d + 2) := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hqpos : 0 < Nat.card F ^ 3 := pow_pos (Nat.zero_lt_of_lt hq) 3
  have hlarge : 2 * Nat.card F ^ 2 ≤ Nat.card F ^ 3 := by
    calc
      2 * Nat.card F ^ 2 ≤ Nat.card F * Nat.card F ^ 2 :=
        Nat.mul_le_mul_right (Nat.card F ^ 2) hq
      _ = Nat.card F ^ 3 := by ring
  have hcount := boundedSolution_cubicExtension_sub_mul_le Q (Nat.card F ^ 2) Δ
    hQ hchar hWeight hDegree
  have hhalf : Nat.card (BoundedSolution Q D) ≤
      2 * (((d + 1) * Δ * Δ) * (Nat.card F ^ 3) ^ d) := by
    apply card_le_two_mul_of_sub_mul_le hqpos hlarge
    calc
      (Nat.card F ^ 3 - Nat.card F ^ 2) * Nat.card (BoundedSolution Q D)
          ≤ ((d + 1) * Δ) *
              (Nat.card F ^ 3 * Δ * (Nat.card F ^ 3) ^ d) := hcount
      _ = Nat.card F ^ 3 * (((d + 1) * Δ * Δ) * (Nat.card F ^ 3) ^ d) := by ring
  calc
    Nat.card (BoundedSolution Q D)
        ≤ 2 * (((d + 1) * Δ * Δ) * (Nat.card F ^ 3) ^ d) := hhalf
    _ ≤ 2 * (((d + 1) * Nat.card F * Nat.card F) * (Nat.card F ^ 3) ^ d) := by
      gcongr
    _ = 2 * (d + 1) * Nat.card F ^ (3 * d + 2) := by
      rw [pow_add, pow_mul]
      ring

/-- Consumer form of the fixed-exponent root bound.  The characteristic contract itself supplies
the uniform individual-degree bound needed by the recursive count, since the characteristic of a
finite field is at most its cardinality. -/
theorem natCard_boundedSolution_le_two_mul_pow_of_weightedDegree [Field F] [Finite F]
    (Q : DifferentialPolynomial F d)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q ≤ Nat.card F ^ 2) :
    Nat.card (BoundedSolution Q D) ≤
      2 * (d + 1) * Nat.card F ^ (3 * d + 2) := by
  let _ := Fintype.ofFinite F
  have hCharCard : ringChar F ≤ Nat.card F := by
    obtain ⟨extensionDegree, _hprime, hcard⟩ :=
      FiniteField.card F (ringChar F)
    apply Nat.le_of_dvd Nat.card_pos
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self _ extensionDegree.ne_zero
  apply natCard_boundedSolution_le_two_mul_pow Q (Nat.card F) hQ hchar hWeight
  · intro s
    exact (hchar.2 s).le.trans hCharCard
  · exact le_rfl

end

end ReedSolomon.HiddenDerivative
