/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Basic
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Coordinates

/-!
# Local rank for the lower-cutoff weighted support

The original higher-derivative factors survive local substitution. Together with the total
cutoff, their lower degree bound limits the first-derivative exponent of every reachable
coordinate. The other constraints retain contact order and higher-jet weight.

These five inequalities embed the actual image in a finite coordinate space. Counting that
space bounds rank without asserting independence of its coordinates, in every characteristic.
-/

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {R : Type*} [CommRing R] {d D m W Cmin : ℕ} {L : ℝ}

/-- Every reachable coordinate obeys the five inequalities used in the weighted rank count. -/
theorem weightedSupport_localConstraint_support (hD : 0 < D) (center received : R)
    {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ weightedSupportSpace R D d W Cmin L hD)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e (localE d) ≤ e (localT d) ∧
      Finsupp.weight (localHigherJetWeight d) e ≤ W + (e (localT d) - e (localE d)) ∧
      localContactOrder d e < m ∧ Cmin ≤ reachableLocalHigherDegree e ∧
      (reachableLocalJetDegree e : ℝ) < L / D := by
  have hs := mem_weightedSupportSpace_iff.mp hQ
  exact localConstraint_support_of_weight_bounds center received
    (fun u hu ↦ (hs u hu).1) (fun u hu ↦ (hs u hu).2.1)
    (fun u hu ↦ totalJetDegree_lt_of_weightedSupportEligible hD (hs u hu)) he

/-- The finite potential-coordinate budget contains the actual local image. -/
theorem weightedSupport_localConstraint_mem_exponents (hd : 0 < d) (hD : 0 < D)
    (center received : R) {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ weightedSupportSpace R D d W Cmin L hD)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e ∈ localBudgetExponents hd m W ⌈L / D - Cmin⌉₊ := by
  obtain ⟨hb, hw, hc, hl, ht⟩ := weightedSupport_localConstraint_support hD center received hQ he
  exact mem_localBudgetExponents_of_bounds hd hb hw hc hl ht

/-- The actual local constraint map on the lower-cutoff support. -/
def weightedSupportLocalConstraint (m : ℕ) (hD : 0 < D) (center received : R) :
    weightedSupportSpace R D d W Cmin L hD →ₗ[R] LocalPolynomial R d :=
  (localConstraintAt m center received).domRestrict _

/-- Counting potential local coordinates bounds the actual local rank over every field. -/
theorem finrank_weightedSupportLocalConstraint_le {F : Type*} [Field F]
    (hd : 0 < d) (hD : 0 < D) (center received : F) :
    Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W)
        (Cmin := Cmin) (L := L) m hD center received)) ≤
      localCoordinateBudget d m W ⌈L / D - Cmin⌉₊ := by
  let s := localBudgetExponents hd m W ⌈L / D - Cmin⌉₊
  let V := MvPolynomial.restrictSupport F (s : Set (LocalVariable d →₀ ℕ))
  let b := MvPolynomial.basisRestrictSupport (R := F) (s : Set (LocalVariable d →₀ ℕ))
  let _ : Module.Finite F V := Module.Finite.of_basis b
  have hdim : Module.finrank F V = s.card := by
    rw [← Fintype.card_coe]
    exact Module.finrank_eq_card_basis b
  have hsubset : LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W)
        (Cmin := Cmin) (L := L) m hD center received) ≤ V := by
    rintro _ ⟨Q, rfl⟩
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro e he
    exact weightedSupport_localConstraint_mem_exponents hd hD center received Q.2 he
  exact (Submodule.finrank_mono hsubset).trans (hdim.le.trans
    (card_localBudgetExponents_le hd m W ⌈L / D - Cmin⌉₊))

end
end ReedSolomon.HiddenDerivative
