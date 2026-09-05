/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Symbolic.Equation

/-!
# A stage-free first-order symbolic MCA envelope

For a first-order equation, every separant stage has order zero or one, its total jet
degree is bounded by that of the original equation, and the number of stages is bounded
by the same total jet degree.  This file packages those facts into one computable bound
that does not expose the separant-chain stages.
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

open Polynomial MvPolynomial SymbolicSeparantChain ReedSolomon

universe u

variable {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
  [IsAlgClosed E] {n A k : ℕ} {domain : Fin n ↪ F} {f g : Fin n → F}

/-- A computable upper envelope for all regular stages of a first-order symbolic equation. -/
def firstOrderSymbolicMCAEnvelope (n K k L A μ h : ℕ) : ℚ :=
  (h : ℚ) + (μ : ℚ) *
    (((μ + h : ℕ) : ℚ) *
        max 1 (((n * (1 + 2 * K * (μ - 1 + h)) : ℕ) : ℚ) /
          ((A - L + 1 : ℕ) : ℚ)) ^ 2 +
      ((n - L : ℕ) : ℚ) * (μ : ℚ) *
        max 1 (((n * (1 + 2 * K * (μ - 1)) : ℕ) : ℚ) /
          ((L - k + 1 : ℕ) : ℚ)))

private theorem regularSymbolicMCABound_firstOrder_le
    (n K k L A μ h v r : ℕ) (hr : r ≤ 1) (hv : v ≤ μ) :
    regularSymbolicMCABound n r K k L A v h ≤
      ((μ + h : ℕ) : ℚ) *
          max 1 (((n * (1 + 2 * K * (μ - 1 + h)) : ℕ) : ℚ) /
            ((A - L + 1 : ℕ) : ℚ)) ^ 2 +
        ((n - L : ℕ) : ℚ) * (μ : ℚ) *
          max 1 (((n * (1 + 2 * K * (μ - 1)) : ℕ) : ℚ) /
            ((L - k + 1 : ℕ) : ℚ)) := by
  let Rv : ℚ := ((n * (1 + 2 * K * (v - 1 + h)) : ℕ) : ℚ) /
    ((A - L + 1 : ℕ) : ℚ)
  let R : ℚ := ((n * (1 + 2 * K * (μ - 1 + h)) : ℕ) : ℚ) /
    ((A - L + 1 : ℕ) : ℚ)
  let Sv : ℚ := ((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
    ((L - k + 1 : ℕ) : ℚ)
  let S : ℚ := ((n * (1 + 2 * K * (μ - 1)) : ℕ) : ℚ) /
    ((L - k + 1 : ℕ) : ℚ)
  have hRv : Rv ≤ R := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.mul_le_mul_left n
      (Nat.add_le_add_left (Nat.mul_le_mul_left (2 * K)
        (Nat.add_le_add_right (Nat.sub_le_sub_right hv 1) h)) 1)
  have hSv : Sv ≤ S := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.mul_le_mul_left n
      (Nat.add_le_add_left (Nat.mul_le_mul_left (2 * K)
        (Nat.sub_le_sub_right hv 1)) 1)
  have hRvnonneg : 0 ≤ Rv := by positivity
  have hSvnonneg : 0 ≤ Sv := by positivity
  have hRmax : Rv ≤ max 1 R := hRv.trans (le_max_right _ _)
  have hSmax : Sv ≤ max 1 S := hSv.trans (le_max_right _ _)
  have hRone : 1 ≤ max 1 R := le_max_left _ _
  have hSone : 1 ≤ max 1 S := le_max_left _ _
  have hRpow : Rv ^ (r + 1) ≤ (max 1 R) ^ 2 := by
    exact (pow_le_pow_left₀ hRvnonneg hRmax _).trans
      (pow_le_pow_right₀ hRone (by omega : r + 1 ≤ 2))
  have hSpow : Sv ^ r ≤ max 1 S := by
    have hp := (pow_le_pow_left₀ hSvnonneg hSmax r).trans
      (pow_le_pow_right₀ hSone hr)
    simpa using hp
  have hvh : ((v + h : ℕ) : ℚ) ≤ ((μ + h : ℕ) : ℚ) := by exact_mod_cast Nat.add_le_add_right hv h
  have hvq : (v : ℚ) ≤ (μ : ℚ) := by exact_mod_cast hv
  unfold regularSymbolicMCABound
  change ((v + h : ℕ) : ℚ) * Rv ^ (r + 1) +
      ((n - L : ℕ) : ℚ) * ((v : ℚ) * Sv ^ r) ≤ _
  apply add_le_add
  · exact mul_le_mul hvh hRpow (by positivity) (by positivity)
  · calc
      ((n - L : ℕ) : ℚ) * ((v : ℚ) * Sv ^ r) ≤
          ((n - L : ℕ) : ℚ) * ((μ : ℚ) * max 1 S) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul hvq hSpow (by positivity) (by positivity)
      _ = ((n - L : ℕ) : ℚ) * (μ : ℚ) * max 1 S := by ring

/-- A first-order sound symbolic equation has one stage-independent exceptional set.
The conclusion retains exact equality of the full agreement set with a base-field pair. -/
theorem exists_exceptional_firstOrderSymbolicLineMCA_of_equation
    (Q : DifferentialPolynomial F[X] 1) (iota : F →+* E)
    (μ h : ℕ) (hne : Q ≠ 0) (hweight : jetWeight Q ≤ μ)
    (hheight : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h)
    (hsound : ∀ z, ∀ P : E[X], P.degree < k →
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (fun i ↦ iota (f i) + z * iota (g i)) P).card →
      differentialSpecialization (map (Polynomial.eval₂RingHom iota z) Q) P = 0)
    (K L : ℕ) (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ μ < ringChar F)
    (hbin : ∀ r ≤ 1, ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ firstOrderSymbolicMCAEnvelope n K k L A μ h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (fun i ↦ iota (f i) + z * iota (g i)) P).card →
        HasExactCorrelatedPair domain f g iota k z P := by
  obtain ⟨stages, terminal, hc, exceptional, hcard, hexact⟩ :=
    exists_exceptional_symbolicLineMCA_of_equation Q iota h hne hweight hheight hsound
      K L hK hkK hk hkL hLA hAn hchar hbin
  refine ⟨exceptional, hcard.trans ?_, hexact⟩
  let C : ℚ := ((μ + h : ℕ) : ℚ) *
      max 1 (((n * (1 + 2 * K * (μ - 1 + h)) : ℕ) : ℚ) /
        ((A - L + 1 : ℕ) : ℚ)) ^ 2 +
    ((n - L : ℕ) : ℚ) * (μ : ℚ) *
      max 1 (((n * (1 + 2 * K * (μ - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ))
  have hstage : ∀ stage ∈ stages.toFinset,
      regularSymbolicMCABound n stage.2.val K k L A (jetWeight stage.1) h ≤ C := by
    intro stage hs
    apply regularSymbolicMCABound_firstOrder_le
    · exact Fin.is_le stage.2
    · exact (hc.stage_contract stage (List.mem_toFinset.mp hs)).2.2.1.trans hweight
  have hsum : ∑ stage ∈ stages.toFinset,
      regularSymbolicMCABound n stage.2.val K k L A (jetWeight stage.1) h ≤
        (stages.toFinset.card : ℚ) * C := by
    calc
      _ ≤ ∑ _stage ∈ stages.toFinset, C := Finset.sum_le_sum hstage
      _ = (stages.toFinset.card : ℚ) * C := by simp
  have hcardStages : (stages.toFinset.card : ℚ) ≤ (μ : ℚ) := by
    have hcardNat : stages.toFinset.card ≤ μ :=
      (List.toFinset_card_le stages).trans (hc.length_le.trans hweight)
    exact_mod_cast hcardNat
  rw [firstOrderSymbolicMCAEnvelope]
  change (h : ℚ) + ∑ stage ∈ stages.toFinset,
      regularSymbolicMCABound n stage.2.val K k L A (jetWeight stage.1) h ≤
        (h : ℚ) + (μ : ℚ) * C
  exact add_le_add le_rfl
    (hsum.trans (mul_le_mul_of_nonneg_right hcardStages (by
      dsimp only [C]
      positivity)))

end ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
