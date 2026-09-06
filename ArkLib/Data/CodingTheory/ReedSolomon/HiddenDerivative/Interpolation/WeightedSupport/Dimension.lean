/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Basic
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.DimensionBridge
import ArkLib.ToMathlib.Combinatorics.CubicStaircase

/-!
# Counting coefficients in the lower-cutoff support

Fixing the higher-derivative exponents leaves a strict degree budget for `X`, `Y₀`, and `Y₁`.
The cubic staircase slots give distinct actual monomials within that budget. Summing over the
eligible higher tuples yields the weighted dimension count used by the integral comparison.
-/

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- Higher-derivative tuples satisfying the weighted cutoff and the single lower cutoff. -/
def weightedSupportHigherTuples (d W Cmin : ℕ) : Finset (HigherJetTuple d) :=
  (weightedHigherJetTuples d W).filter fun c ↦ Cmin ≤ higherJetTupleDegree c

@[simp] theorem mem_weightedSupportHigherTuples {d W Cmin : ℕ} {c : HigherJetTuple d} :
    c ∈ weightedSupportHigherTuples d W Cmin ↔
      higherJetTupleWeight c ≤ W ∧ Cmin ≤ higherJetTupleDegree c := by
  simp [weightedSupportHigherTuples]

/-- A higher tuple and one of its available three-exponent slots. -/
def WeightedSupportSlot (D d W Cmin : ℕ) (L : ℝ) :=
  Σ c : ↥(weightedSupportHigherTuples d W Cmin),
    CubicStaircase.Slot D (L / D - higherJetTupleDegree c.val)

/-- The actual monomial represented by a weighted slot. -/
def weightedSupportSlotExponent {D d W Cmin : ℕ} {L : ℝ} (hd : 0 < d)
    (a : WeightedSupportSlot D d W Cmin L) : JetVariable d →₀ ℕ :=
  (exactExponentCoordinatesEquiv hd).symm
    (a.2.exponents.1, ((a.2.exponents.2.1, a.2.exponents.2.2), a.1.val))

/-- Every slot gives a monomial in the lower-cutoff support. -/
theorem weightedSupportSlotExponent_eligible {D d W Cmin : ℕ} {L : ℝ}
    (hd : 0 < d) (hD : 0 < D) (a : WeightedSupportSlot D d W Cmin L) :
    WeightedSupportEligible D d W Cmin L (weightedSupportSlotExponent hd a) := by
  have hc := mem_weightedSupportHigherTuples.mp a.1.property
  have hslot := CubicStaircase.Slot.weighted_degree_lt a.2
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hcancel : (D : ℝ) * (L / D - higherJetTupleDegree a.1.val) =
      L - D * higherJetTupleDegree a.1.val := by field_simp
  rw [hcancel] at hslot
  unfold WeightedSupportEligible
  rw [fullHigherJetWeight_eq_coordinate hd, fullHigherJetDegree_eq_coordinates hd,
    totalJetDegree_eq_coordinates hd]
  simp only [weightedSupportSlotExponent, Equiv.apply_symm_apply]
  refine ⟨hc.1, hc.2, ?_⟩
  have hx : (weightedSupportSlotExponent hd a) none = a.2.exponents.1 := by
    have he := exactExponentCoordinatesEquiv_x hd (weightedSupportSlotExponent hd a)
    simpa [weightedSupportSlotExponent] using he.symm
  dsimp only [weightedSupportSlotExponent] at hx
  rw [hx]
  push_cast at hslot ⊢
  nlinarith only [hslot]


/-- Different weighted slots represent different monomials. -/
theorem weightedSupportSlotExponent_injective {D d W Cmin : ℕ} {L : ℝ} (hd : 0 < d) :
    Function.Injective (weightedSupportSlotExponent (D := D) (W := W)
      (Cmin := Cmin) (L := L) hd) := by
  rintro ⟨c, s⟩ ⟨e, t⟩ h
  have hh := congrArg (exactExponentCoordinatesEquiv hd) h
  simp only [weightedSupportSlotExponent, Equiv.apply_symm_apply] at hh
  have hc : c = e := Subtype.ext (congrArg (fun p ↦ p.2.2) hh)
  subst e
  have hx : s.exponents.1 = t.exponents.1 :=
    congrArg (fun p : ExactExponentCoordinates d ↦ p.1) hh
  have hb : s.exponents.2 = t.exponents.2 :=
    congrArg (fun p : ExactExponentCoordinates d ↦ p.2.1) hh
  have hs : s.exponents = t.exponents := Prod.ext hx hb
  exact congrArg (Sigma.mk c) (CubicStaircase.Slot.exponents_injective _ _ hs)

instance (D d W Cmin : ℕ) (L : ℝ) : Fintype (WeightedSupportSlot D d W Cmin L) :=
  inferInstanceAs (Fintype (Σ c : ↥(weightedSupportHigherTuples d W Cmin),
    CubicStaircase.Slot D (L / D - higherJetTupleDegree c.val)))

/-- Counting the slots never exceeds the dimension of the actual supported monomial space. -/
theorem card_weightedSupportSlot_le {D d W Cmin : ℕ} {L : ℝ}
    (hd : 0 < d) (hD : 0 < D) :
    Fintype.card (WeightedSupportSlot D d W Cmin L) ≤
      (weightedSupportExponents D d W Cmin L hD).card := by
  let f : WeightedSupportSlot D d W Cmin L →
      ↥(weightedSupportExponents D d W Cmin L hD) := fun a ↦
    ⟨weightedSupportSlotExponent hd a,
      mem_weightedSupportExponents.mpr (weightedSupportSlotExponent_eligible hd hD a)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply weightedSupportSlotExponent_injective hd
    exact congrArg Subtype.val hab
  simpa using Fintype.card_le_of_injective f hf


/-- The dependent slot count is the sum of the exact cubic staircase counts. -/
theorem card_weightedSupportSlot_eq (D d W Cmin : ℕ) (L : ℝ) :
    Fintype.card (WeightedSupportSlot D d W Cmin L) =
      ∑ c ∈ weightedSupportHigherTuples d W Cmin,
        CubicStaircase.count D (L / D - higherJetTupleDegree c) := by
  change Fintype.card (Σ c : ↥(weightedSupportHigherTuples d W Cmin),
    CubicStaircase.Slot D (L / D - higherJetTupleDegree c.val)) = _
  rw [Fintype.card_sigma]
  simp_rw [CubicStaircase.card_slot]
  exact Finset.sum_coe_sort (weightedSupportHigherTuples d W Cmin)
    (fun c ↦ CubicStaircase.count D (L / D - higherJetTupleDegree c))

/-- The actual polynomial space has at least the sum of the cubic residual contributions. -/
theorem weightedSupport_dimension_ge_cubic_sum (F : Type*) [Field F]
    {D d W Cmin : ℕ} {L : ℝ} (hd : 0 < d) (hD : 0 < D) :
    (∑ c ∈ weightedSupportHigherTuples d W Cmin,
      (D : ℝ) * (max (L / D - higherJetTupleDegree c) 0) ^ 3 / 6) ≤
      (Module.finrank F (weightedSupportSpace F D d W Cmin L hD) : ℝ) := by
  have hslots := card_weightedSupportSlot_le (W := W) (Cmin := Cmin) (L := L) hd hD
  rw [card_weightedSupportSlot_eq] at hslots
  rw [finrank_weightedSupportSpace_eq_card]
  calc
    _ ≤ ∑ c ∈ weightedSupportHigherTuples d W Cmin,
        (CubicStaircase.count D (L / D - higherJetTupleDegree c) : ℝ) :=
      Finset.sum_le_sum fun c _ ↦ CubicStaircase.count_ge_cubic _ _
    _ ≤ (weightedSupportExponents D d W Cmin L hD).card := by
      exact_mod_cast hslots

end
end ReedSolomon.HiddenDerivative
