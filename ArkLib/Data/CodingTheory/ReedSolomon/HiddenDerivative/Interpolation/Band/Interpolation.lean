/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Band.LocalRank


/-!
# Global interpolation from the asymmetric-band certificate

The proved local rank bound applies to the band subspace, not to the larger exact interpolation
space. We take the product of the actual band-restricted maps and use rank-nullity on this finite
domain. A strict numerical dimension certificate therefore produces a nonzero band polynomial
satisfying every received-point constraint. Only afterward do we include it in the exact space.

This is an existence theorem, not an executable linear solver. The strict finite dimension
inequality remains an explicit premise, to be supplied by the uniform parameter analysis.
-/

open PolynomialDifferential


noncomputable section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]
variable {D d m W Cmin Cmax : ℕ} {L : ℝ}

/-- Product of the actual local maps on the common band domain. -/
def asymmetricBandGlobalConstraint (hD : 0 < D) (centers received : ι → F) :
    asymmetricBandSpace F D d m W Cmin Cmax L hD →ₗ[F] (ι → LocalPolynomial F d) :=
  LinearMap.pi fun i ↦ asymmetricBandLocalConstraint hD (centers i) (received i)

/-- The product map has rank at most the number of received positions times the proved
pointwise band budget. No finite-dimensionality of the ambient polynomial codomain is assumed. -/
theorem finrank_asymmetricBandGlobalConstraint_le (hd : 0 < d) (hD : 0 < D)
    (centers received : ι → F) :
    Module.finrank F (asymmetricBandGlobalConstraint (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD centers received).range ≤
        Fintype.card ι * localCoordinateBudget d m W ⌈L / D - Cmin⌉₊ := by
  let V := asymmetricBandSpace F D d m W Cmin Cmax L hD
  let : Module.Finite F V := Module.Finite.of_basis (asymmetricBandBasis hD)
  let φ := fun i ↦ asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
    (Cmin := Cmin) (Cmax := Cmax) (L := L) hD (centers i) (received i)
  let Φ := asymmetricBandGlobalConstraint (d := d) (m := m) (W := W)
    (Cmin := Cmin) (Cmax := Cmax) (L := L) hD centers received
  let includeRange : Φ.range →ₗ[F] (∀ i, (φ i).range) := {
    toFun y i := ⟨y.1 i, by
      rcases y.2 with ⟨v, hv⟩
      exact ⟨v, congrFun hv i⟩⟩
    map_add' x y := by ext i; rfl
    map_smul' a x := by ext i; rfl
  }
  have hinj : Function.Injective includeRange := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  calc
    Module.finrank F Φ.range ≤ Module.finrank F (∀ i, (φ i).range) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    _ = ∑ i, Module.finrank F (φ i).range := Module.finrank_pi_fintype F
    _ ≤ ∑ _i : ι, localCoordinateBudget d m W ⌈L / D - Cmin⌉₊ :=
      Finset.sum_le_sum fun i _ ↦
        finrank_asymmetricBandLocalConstraint_le hd hD (centers i) (received i)
    _ = _ := by simp

/-- The strict finite band certificate yields a genuine nonzero interpolant with every local
constraint, over any field and any indexed collection of received positions. -/
theorem exists_nonzero_band_interpolant (hd : 0 < d) (hD : 0 < D)
    (centers received : ι → F)
    (hdim : Fintype.card ι * localCoordinateBudget d m W ⌈L / D - Cmin⌉₊ <
      asymmetricBandDimensionCount D d m W Cmin Cmax L) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧
      Q ∈ asymmetricBandSpace F D d m W Cmin Cmax L hD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  let V := asymmetricBandSpace F D d m W Cmin Cmax L hD
  let : Module.Finite F V := Module.Finite.of_basis (asymmetricBandBasis hD)
  let Φ := asymmetricBandGlobalConstraint (d := d) (m := m) (W := W)
    (Cmin := Cmin) (Cmax := Cmax) (L := L) hD centers received
  have hrank : Module.finrank F Φ.range < Module.finrank F V := by
    rw [finrank_asymmetricBandSpace_eq_dimensionCount hd hD]
    exact (finrank_asymmetricBandGlobalConstraint_le hd hD centers received).trans_lt hdim
  have hnull := LinearMap.finrank_range_add_finrank_ker Φ
  change Module.finrank F Φ.range + Module.finrank F Φ.ker = Module.finrank F V at hnull
  have hpos : 0 < Module.finrank F Φ.ker := by omega
  have hker : Φ.ker ≠ ⊥ := by
    intro h
    rw [h] at hpos
    simp at hpos
  obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v.1, ?_, v.2, ?_⟩
  · intro hv
    exact hv0 (Subtype.ext hv)
  · intro i
    have hi := congrFun (LinearMap.mem_ker.mp hvker) i
    exact hi

/-- Include the band interpolant in the existing exact-space interface, preserving its nonzero
value and all local constraints. This is the bridge to the specialization and root-count proofs. -/
theorem exists_nonzero_exact_interpolant_of_band_certificate {A : ℕ}
    (hd : 0 < d) (hdD : d < D) (centers received : ι → F)
    (hL : L ≤ (m * A : ℕ))
    (hdim : Fintype.card ι * localCoordinateBudget d m W ⌈L / D - Cmin⌉₊ <
      asymmetricBandDimensionCount D d m W Cmin Cmax L) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧
      Q ∈ exactInterpolationSpace F D A d m m W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  obtain ⟨Q, hQ0, hQband, hQlocal⟩ :=
    exists_nonzero_band_interpolant hd (hd.trans hdD) centers received hdim
  exact ⟨Q, hQ0,
    asymmetricBandSpace_le_exactInterpolationSpace (hd.trans hdD) hdD hL hQband, hQlocal⟩

end ReedSolomon.HiddenDerivative
