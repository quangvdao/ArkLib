/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Basic
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Contact
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Rank


/-!
# First-order interpolation certificates

The capped support is connected here to the actual hidden-derivative local constraint map.
Restriction cannot increase rank, so the existing exhibited-kernel theorem supplies a uniform
local rank certificate.  Rank--nullity then turns the finite inequality `N > n r` into a nonzero
polynomial satisfying every received-point constraint.
-/

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

variable {F : Type*} [Field F]
variable {D A m M μ : ℕ}
variable {ι : Type*} [Fintype ι]

/-- The actual local constraint map restricted to the capped first-order support. -/
def firstOrderLocalConstraintAt (center received : F) :
    firstOrderSpace F D A m M μ →ₗ[F] LocalPolynomial F 1 :=
  (localConstraintAt (d := 1) m center received).domRestrict
    (firstOrderSpace F D A m M μ)

/-- Restricting to the capped first-order support cannot exceed the certified rank of the exact
first-order local constraint map. -/
theorem finrank_firstOrderLocalConstraintAt_le (hD : 1 < D)
    (center received : F) :
    Module.finrank F (LinearMap.range
      (firstOrderLocalConstraintAt (D := D) (A := A) (m := m) (M := M) (μ := μ)
        center received)) ≤ certifiedEnlargedRankBound 1 m M 0 := by
  let exactBasis := exactInterpolationSpaceBasis F D A 1 m M 0 hD
  let _ : Module.Finite F (exactInterpolationSpace F D A 1 m M 0 hD) :=
    Module.Finite.of_basis exactBasis
  let embedding : firstOrderSpace F D A m M μ →ₗ[F]
      exactInterpolationSpace F D A 1 m M 0 hD :=
    Submodule.inclusion (firstOrderSpace_le_exactInterpolationSpace hD)
  have hfactor :
      firstOrderLocalConstraintAt (D := D) (A := A) (m := m) (M := M) (μ := μ)
          center received =
        (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := 0)
          hD m center received).comp embedding := by
    ext Q
    rfl
  rw [hfactor]
  exact (finrank_range_comp_le_outer
    (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := 0)
      hD m center received) embedding).trans
      (finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound
        (by omega : 0 < 1) hD center received)

/-- All first-order local constraints over a finite received word. -/
def firstOrderGlobalConstraint (centers received : ι → F) :
    firstOrderSpace F D A m M μ →ₗ[F]
      (∀ _ : ι, LocalPolynomial F 1) :=
  LinearMap.pi fun i ↦ firstOrderLocalConstraintAt (centers i) (received i)

/-- The global constraint rank is bounded by the number of points times the uniform local
certificate. -/
theorem finrank_firstOrderGlobalConstraint_le (hD : 1 < D)
    (centers received : ι → F) :
    Module.finrank F (LinearMap.range
      (firstOrderGlobalConstraint (D := D) (A := A) (m := m) (M := M) (μ := μ)
        centers received)) ≤
      Fintype.card ι * certifiedEnlargedRankBound 1 m M 0 := by
  let b := firstOrderSpaceBasis F D A m M μ
  let _ : Module.Finite F (firstOrderSpace F D A m M μ) :=
    Module.Finite.of_basis b
  let φ := fun i ↦ firstOrderLocalConstraintAt
    (D := D) (A := A) (m := m) (M := M) (μ := μ) (centers i) (received i)
  let Φ := firstOrderGlobalConstraint
    (D := D) (A := A) (m := m) (M := M) (μ := μ) centers received
  let includeRange : Φ.range →ₗ[F] (∀ i, (φ i).range) := {
    toFun y i := ⟨y.1 i, by
      rcases y.2 with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      rw [← hv]
      rfl⟩
    map_add' x y := by ext i; rfl
    map_smul' a x := by ext i; rfl
  }
  have hinjective : Function.Injective includeRange := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  calc
    Module.finrank F Φ.range ≤ Module.finrank F (∀ i, (φ i).range) :=
      LinearMap.finrank_le_finrank_of_injective hinjective
    _ = ∑ i, Module.finrank F (φ i).range := Module.finrank_pi_fintype F
    _ ≤ ∑ _ : ι, certifiedEnlargedRankBound 1 m M 0 := by
      apply Finset.sum_le_sum
      intro i _
      exact finrank_firstOrderLocalConstraintAt_le hD (centers i) (received i)
    _ = Fintype.card ι * certifiedEnlargedRankBound 1 m M 0 := by simp

/-- A checked finite inequality produces a nonzero capped first-order interpolant satisfying the
actual local monomial constraints at every received point. -/
theorem exists_nonzero_firstOrder_interpolant (hD : 1 < D)
    (centers received : ι → F)
    (hdim : Fintype.card ι * certifiedEnlargedRankBound 1 m M 0 <
      (firstOrderExponents D A m M μ).card) :
    ∃ Q : DifferentialPolynomial F 1,
      Q ≠ 0 ∧
      Q ∈ firstOrderSpace F D A m M μ ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  let V := firstOrderSpace F D A m M μ
  let Φ := firstOrderGlobalConstraint
    (D := D) (A := A) (m := m) (M := M) (μ := μ) centers received
  let b := firstOrderSpaceBasis F D A m M μ
  let _ : Module.Finite F V := Module.Finite.of_basis b
  have hdimV : Module.finrank F V =
      (firstOrderExponents D A m M μ).card := by
    simpa [V] using
      (finrank_firstOrderSpace_eq_card (F := F) (D := D) (A := A) (m := m)
        (M := M) (μ := μ))
  have hrank : Module.finrank F Φ.range < Module.finrank F V := by
    apply (finrank_firstOrderGlobalConstraint_le hD centers received).trans_lt
    rw [hdimV]
    exact hdim
  have hnull := LinearMap.finrank_range_add_finrank_ker Φ
  change Module.finrank F Φ.range + Module.finrank F Φ.ker =
    Module.finrank F V at hnull
  have hkerpos : 0 < Module.finrank F Φ.ker := by omega
  have hker : Φ.ker ≠ ⊥ := by
    intro h
    rw [h] at hkerpos
    simp at hkerpos
  obtain ⟨Q, hQker, hQ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨Q.1, ?_, Q.2, ?_⟩
  · intro h
    apply hQ0
    apply Subtype.ext
    exact h
  · intro i
    have hi := congrFun (LinearMap.mem_ker.mp hQker) i
    simpa [Φ, firstOrderGlobalConstraint, firstOrderLocalConstraintAt,
      SatisfiesLocalConstraints] using hi

/-- The finite first-order certificate is sound for polynomial agreement: at every certified
received point, specialization at an agreeing polynomial has a root of multiplicity `m`. -/
theorem exists_nonzero_firstOrder_interpolant_with_multiplicity (hD : 1 < D)
    (centers received : ι → F)
    (hdim : Fintype.card ι * certifiedEnlargedRankBound 1 m M 0 <
      (firstOrderExponents D A m M μ).card)
    (P : Polynomial F) (hagree : ∀ i, P.eval (centers i) = received i) :
    ∃ Q : DifferentialPolynomial F 1,
      Q ≠ 0 ∧
      Q ∈ firstOrderSpace F D A m M μ ∧
      ∀ i, (Polynomial.X - Polynomial.C (centers i)) ^ m ∣
        differentialSpecialization Q P := by
  obtain ⟨Q, hQ0, hQmem, hQconstraints⟩ :=
    exists_nonzero_firstOrder_interpolant hD centers received hdim
  refine ⟨Q, hQ0, hQmem, fun i ↦ ?_⟩
  exact X_sub_C_pow_dvd_differentialSpecialization_of_contact
    Q P (centers i) (received i) (hagree i) (hQconstraints i)

end

end ReedSolomon.HiddenDerivative
