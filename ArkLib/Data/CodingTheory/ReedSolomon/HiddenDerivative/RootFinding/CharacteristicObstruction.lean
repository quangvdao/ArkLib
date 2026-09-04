/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.DifferentialEquation
import Mathlib.Algebra.Field.ZMod

/-!
# Bounded-characteristic obstruction to regular-jet uniqueness

This file records an elementary boundary example for regular coefficient lifting.  Over
`ZMod p`, the differential equation `Y₁ = 0` has nonzero separant, but both `0` and `X ^ p`
are solutions of degree at most `D` when `p ≤ D`.  Their order-one Hasse jets agree at the origin.
Consequently, polynomial jets are not injective even on the regular bounded solutions.

The example pinpoints the failed hypothesis in the below-characteristic specialization used by
the root solver: `D < ringChar (ZMod p)` is false.  The differential equation's individual jet
degrees are still below the characteristic.  At the corresponding lift step `k = p - 1`, `r = 1`,
the multiplier `choose (k + r) r` is `p`, hence zero in `ZMod p`.

This is an elementary regression counterexample, not a theorem claimed by [Kop15].  In general
characteristic, [Kop15, Corollary 4.5] permits branching at such resonant steps; uniqueness is the
additional below-characteristic specialization used by this development.  Nothing here asserts
failure of root finding or of the source's general-characteristic count.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15]
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

variable (p D : ℕ) [Fact p.Prime]

/-! ### The characteristic-`p` equation and its solutions -/

/-- The depth-one differential equation `Y₁ = 0` over `ZMod p`. -/
def characteristicFirstJetEquation : DifferentialPolynomial (ZMod p) 1 :=
  MvPolynomial.X (some (1 : Fin 2))

/-- The zero polynomial as a bounded solution of `Y₁ = 0`. -/
def zeroFirstJetSolution : BoundedSolution (characteristicFirstJetEquation p) D := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  · simp
  · simp [characteristicFirstJetEquation, differentialSpecialization]

/-- `X ^ p` as a bounded solution of `Y₁ = 0`, when the degree budget reaches `p`. -/
def frobeniusFirstJetSolution (hD : p ≤ D) :
    BoundedSolution (characteristicFirstJetEquation p) D := by
  refine ⟨⟨X ^ p, ?_⟩, ?_⟩
  · rw [Polynomial.mem_degreeLT, degree_X_pow]
    exact_mod_cast Nat.lt_succ_of_le hD
  · simp [characteristicFirstJetEquation, differentialSpecialization,
      X_pow_eq_monomial, hasseDeriv_monomial]

@[simp]
theorem zeroFirstJetSolution_polynomial :
    (zeroFirstJetSolution p D).polynomial = 0 :=
  rfl

@[simp]
theorem frobeniusFirstJetSolution_polynomial (hD : p ≤ D) :
    (frobeniusFirstJetSolution p D hD).polynomial = X ^ p :=
  rfl

/-- The equation has constant nonzero separant in its active coordinate. -/
theorem characteristicFirstJetEquation_separant :
    separant (characteristicFirstJetEquation p) (1 : Fin 2) = 1 := by
  simp [characteristicFirstJetEquation, separant]

/-- The two explicit bounded solutions are distinct. -/
theorem zeroFirstJetSolution_ne_frobenius (hD : p ≤ D) :
    zeroFirstJetSolution p D ≠ frobeniusFirstJetSolution p D hD := by
  intro h
  have hpolynomial := congrArg BoundedSolution.polynomial h
  simp only [zeroFirstJetSolution_polynomial, frobeniusFirstJetSolution_polynomial] at hpolynomial
  exact pow_ne_zero p Polynomial.X_ne_zero hpolynomial.symm

/-! ### Equal regular initial jets -/

/-- At the origin, `0` and `X ^ p` have the same Hasse jet through order one. -/
theorem polynomialJet_zero_eq_polynomialJet_X_pow :
    polynomialJet (d := 1) (0 : ZMod p) 0 = polynomialJet 0 (X ^ p) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  funext j
  fin_cases j
  · change Polynomial.hasseCoeffAt 0 0 0 = Polynomial.hasseCoeffAt 0 0 (X ^ p)
    rw [Polynomial.hasseCoeffAt_zero_eq_coeff, Polynomial.hasseCoeffAt_zero_eq_coeff]
    simp only [coeff_zero, coeff_X_pow]
    split
    · omega
    · rfl
  · change Polynomial.hasseCoeffAt 0 1 0 = Polynomial.hasseCoeffAt 0 1 (X ^ p)
    rw [Polynomial.hasseCoeffAt_zero_eq_coeff, Polynomial.hasseCoeffAt_zero_eq_coeff]
    simp [hp.ne]

/-- The common initial jet is regular: it lies on `Y₁ = 0`, and the separant evaluates to one. -/
theorem characteristicFirstJetEquation_zero_regular :
    IsRegularJet (characteristicFirstJetEquation p) (1 : Fin 2) 0
      (polynomialJet (d := 1) 0 (0 : (ZMod p)[X])) := by
  simp [IsRegularJet, characteristicFirstJetEquation, jetEvaluation, polynomialJet, separant]

/-- A nonvacuous bounded-characteristic obstruction: two distinct bounded solutions have the
same regular initial Hasse jet. -/
theorem exists_distinct_boundedSolutions_with_same_regularJet (hD : p ≤ D) :
    ∃ P₀ Pp : BoundedSolution (characteristicFirstJetEquation p) D,
      P₀ ≠ Pp ∧
        polynomialJet (d := 1) 0 P₀.polynomial = polynomialJet 0 Pp.polynomial ∧
        IsRegularJet (characteristicFirstJetEquation p) (1 : Fin 2) 0
          (polynomialJet 0 P₀.polynomial) ∧
        IsRegularJet (characteristicFirstJetEquation p) (1 : Fin 2) 0
          (polynomialJet 0 Pp.polynomial) := by
  refine ⟨zeroFirstJetSolution p D, frobeniusFirstJetSolution p D hD,
    zeroFirstJetSolution_ne_frobenius p D hD, ?_, ?_, ?_⟩
  · exact polynomialJet_zero_eq_polynomialJet_X_pow p
  · exact characteristicFirstJetEquation_zero_regular p
  · change IsRegularJet (characteristicFirstJetEquation p) (1 : Fin 2) 0
      (polynomialJet (d := 1) 0 (X ^ p))
    rw [← polynomialJet_zero_eq_polynomialJet_X_pow p]
    exact characteristicFirstJetEquation_zero_regular p

/-- The jet encoding used by regular-witness counting is not injective on regular bounded
solutions once the degree budget reaches the characteristic. -/
theorem not_injOn_polynomialJet_regularSolutions (hD : p ≤ D) :
    ¬Set.InjOn
      (fun P : BoundedSolution (characteristicFirstJetEquation p) D ↦
        polynomialJet (d := 1) 0 P.polynomial)
      {P | IsRegularJet (characteristicFirstJetEquation p) (1 : Fin 2) 0
        (polynomialJet 0 P.polynomial)} := by
  intro hinjective
  obtain ⟨P₀, Pp, hne, heq, hregular₀, hregularp⟩ :=
    exists_distinct_boundedSolutions_with_same_regularJet p D hD
  exact hne (hinjective hregular₀ hregularp heq)

/-! ### Exact failed characteristic premise -/

/-- Every individual jet degree of `Y₁` is below the characteristic. -/
theorem characteristicFirstJetEquation_jetDegree_lt_ringChar (j : Fin 2) :
    jetDegree (characteristicFirstJetEquation p) j < ringChar (ZMod p) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  by_cases hj : j = (1 : Fin 2)
  · subst j
    simpa [characteristicFirstJetEquation, jetDegree, ZMod.ringChar_zmod_n] using hp
  · rw [jetDegree, characteristicFirstJetEquation,
      MvPolynomial.degreeOf_X_of_ne (by simpa using hj)]
    simpa [ZMod.ringChar_zmod_n] using (Nat.zero_lt_one.trans hp)

/-- When `p ≤ D`, the ambient-degree conjunct of `IsBelowCharacteristic` fails, while its
individual-jet-degree conjunct remains true. -/
theorem characteristicFirstJetEquation_failed_characteristic_components (hD : p ≤ D) :
    ¬ D < ringChar (ZMod p) ∧
      ∀ j, jetDegree (characteristicFirstJetEquation p) j < ringChar (ZMod p) := by
  constructor
  · simpa [ZMod.ringChar_zmod_n] using not_lt_of_ge hD
  · exact characteristicFirstJetEquation_jetDegree_lt_ringChar p

/-- Thus the precise below-characteristic hypothesis used by regular-jet uniqueness is absent. -/
theorem characteristicFirstJetEquation_not_isBelowCharacteristic (hD : p ≤ D) :
    ¬ IsBelowCharacteristic D (characteristicFirstJetEquation p) := by
  intro h
  exact (characteristicFirstJetEquation_failed_characteristic_components p D hD).1 h.1

/-- The regular lift from order `p - 1` with highest jet `Y₁` is resonant: its binomial
multiplier is zero in `ZMod p`. -/
theorem characteristicFirstJetEquation_resonant_binomial :
    (((p - 1 + 1).choose 1 : ℕ) : ZMod p) = 0 := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [Nat.sub_add_cancel hp, Nat.choose_one_right]
  exact ZMod.natCast_self p

end

end ReedSolomon.HiddenDerivative
