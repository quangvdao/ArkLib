/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Band.Basic

/-!
# Local rank on the asymmetric-band support

The shared reachable-coordinate argument only needs the weighted cutoff, lower higher-jet
cutoff, and total degree cutoff. This module specializes it to the asymmetric-band space.
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d D m W Cmin Cmax : ℕ} {L : ℝ}

/-- Strict total degree survives substitution for the asymmetric-band support. -/
theorem unscaledLocal_jet_degree_lt (hD : 0 < D) (center received : R)
    {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ asymmetricBandSpace R D d m W Cmin Cmax L hD)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    (reachableLocalJetDegree e : ℝ) < L / D := by
  exact unscaled_jet_degree_lt_of_support center received
    (fun u hu ↦ totalJetDegree_lt_of_asymmetricBandEligible hD
      (mem_asymmetricBandSpace_iff.mp hQ u hu)) he


/-- Actual local support satisfies all five inequalities of `band-reachable-coordinates`.
Here `reachableLocalJetDegree` is `h+e+|z|`; no image or rank hypothesis is assumed. -/
theorem asymmetricBand_localConstraint_support (hD : 0 < D) (center received : R)
    {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ asymmetricBandSpace R D d m W Cmin Cmax L hD)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e (localE d) ≤ e (localT d) ∧
      Finsupp.weight (localHigherJetWeight d) e ≤ W + (e (localT d) - e (localE d)) ∧
      localContactOrder d e < m ∧ Cmin ≤ reachableLocalHigherDegree e ∧
      (reachableLocalJetDegree e : ℝ) < L / D := by
  have hs := mem_asymmetricBandSpace_iff.mp hQ
  exact localConstraint_support_of_weight_bounds center received
    (fun u hu ↦ (hs u hu).2.1) (fun u hu ↦ (hs u hu).2.2.1)
    (fun u hu ↦ totalJetDegree_lt_of_asymmetricBandEligible hD (hs u hu)) he


/-- Embed every actually retained band coordinate into the finite local budget. -/
theorem asymmetricBand_localConstraint_mem_exponents (hd : 0 < d) (hD : 0 < D)
    (center received : R) {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ asymmetricBandSpace R D d m W Cmin Cmax L hD)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e ∈ localBudgetExponents hd m W ⌈L / D - Cmin⌉₊ := by
  obtain ⟨hb, hw, hc, hl, ht⟩ := asymmetricBand_localConstraint_support hD center received hQ he
  exact mem_localBudgetExponents_of_bounds hd hb hw hc hl ht


/-- The actual local map restricted to the asymmetric-band polynomial space. -/
def asymmetricBandLocalConstraint (hD : 0 < D) (center received : R) :
    asymmetricBandSpace R D d m W Cmin Cmax L hD →ₗ[R] LocalPolynomial R d :=
  (localConstraintAt m center received).domRestrict _

/-- Actual local rank is bounded by the explicit asymmetric-band coordinate count.
No characteristic assumption, nonempty-band hypothesis, or unproved rank premise is needed. -/
theorem finrank_asymmetricBandLocalConstraint_le {F : Type*} [Field F]
    (hd : 0 < d) (hD : 0 < D) (center received : F) :
    Module.finrank F (LinearMap.range
      (asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received)) ≤
      localCoordinateBudget d m W ⌈L / D - Cmin⌉₊ := by
  let s := localBudgetExponents hd m W ⌈L / D - Cmin⌉₊
  let V := MvPolynomial.restrictSupport F (s : Set (LocalVariable d →₀ ℕ))
  let b := MvPolynomial.basisRestrictSupport (R := F) (s : Set (LocalVariable d →₀ ℕ))
  let _ : Module.Finite F V := Module.Finite.of_basis b
  have hdim : Module.finrank F V = s.card := by
    rw [← Fintype.card_coe]
    exact Module.finrank_eq_card_basis b
  have hsubset : LinearMap.range
      (asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received) ≤ V := by
    rintro _ ⟨Q, rfl⟩
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro e he
    exact asymmetricBand_localConstraint_mem_exponents hd hD center received Q.2 he
  exact (Submodule.finrank_mono hsubset).trans (hdim.le.trans
    (card_localBudgetExponents_le hd m W ⌈L / D - Cmin⌉₊))

end ReedSolomon.HiddenDerivative
