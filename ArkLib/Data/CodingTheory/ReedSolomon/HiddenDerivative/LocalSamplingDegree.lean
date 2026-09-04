/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Substitution
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.AsymmetricBand

/-!
# Individual degree budgets for sampling local constraints

The local substitution may have a large degree in the displacement `T`, but its combined
degree in the error and visible jets never exceeds the original total jet degree. This permits
anisotropic scalar grids: only the displacement grid needs to grow with the block length.

The bounds concern the full, untruncated local polynomial. Thus coefficient recovery may precede
the low-contact projection without losing information. These are algebraic degree bounds, not an
implementation or cost bound for coefficient recovery.
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] {d D B : ℕ}

/-- Weight one on every non-displacement variable, and zero on the distinguished variable. -/
def nonDisplacementWeight {α : Type*} : Option α → ℕ
  | none => 0
  | some _ => 1

/-- On the global variables this is exactly the sum of all jet exponents. -/
theorem weight_nonDisplacement_eq_totalJetDegree (u : JetVariable d →₀ ℕ) :
    Finsupp.weight nonDisplacementWeight u = totalJetDegree u := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, nonDisplacementWeight,
    totalJetDegree, Finsupp.degree_eq_sum, Fintype.sum_option]

private theorem localCorrection_mem_nonDisplacement (d : ℕ) :
    localCorrection (R := R) d ∈
      restrictWeightedDegree (R := R) nonDisplacementWeight 1 := by
  apply Submodule.sum_mem
  intro j _
  have ht := pow_mem_restrictWeightedDegree
    (X_mem_restrictWeightedDegree (R := R) nonDisplacementWeight 0
      (localT d) (by rfl)) (j.val + 1)
  have hc := mul_mem_restrictWeightedDegree
    (C_mem_restrictWeightedDegree (R := R) nonDisplacementWeight 0
      ((-1 : R) ^ j.val)) ht
  simpa using mul_mem_restrictWeightedDegree hc
    (X_mem_restrictWeightedDegree (R := R) nonDisplacementWeight 1
      (localY j) (by rfl))

/-- Each generator image preserves the global total-jet budget. -/
theorem unscaledLocalImage_mem_nonDisplacement (center received : R) (v : JetVariable d) :
    unscaledLocalImage d center received v ∈
      restrictWeightedDegree (R := R) nonDisplacementWeight (nonDisplacementWeight v) := by
  rcases v with _ | j
  · exact Submodule.add_mem _ (C_mem_restrictWeightedDegree _ _ _)
      (X_mem_restrictWeightedDegree _ _ _ (by rfl))
  · refine Fin.cases ?_ (fun i ↦ ?_) j
    · change C received + localCorrection d + X (localT d) * X (localE d) ∈ _
      apply Submodule.add_mem
      · exact Submodule.add_mem _ (C_mem_restrictWeightedDegree _ _ _)
          (localCorrection_mem_nonDisplacement d)
      · simpa only [zero_add, nonDisplacementWeight] using mul_mem_restrictWeightedDegree
          (X_mem_restrictWeightedDegree (R := R) nonDisplacementWeight 0
            (localT d) (by rfl))
          (X_mem_restrictWeightedDegree (R := R) nonDisplacementWeight 1
            (localE d) (by rfl))
    · exact X_mem_restrictWeightedDegree _ _ _ (by rfl)

/-- The sum of error and visible-jet exponents is bounded independently of the `X` degree. -/
theorem unscaledLocalSubstitution_mem_nonDisplacement
    (center received : R) (Q : DifferentialPolynomial R d)
    (hQ : ∀ u ∈ Q.support, totalJetDegree u ≤ B) :
    unscaledLocalSubstitution d center received Q ∈
      restrictWeightedDegree (R := R) nonDisplacementWeight B := by
  apply bind₁_mem_restrictWeightedDegree
    (unscaledLocalImage_mem_nonDisplacement center received)
  simpa only [mem_restrictWeightedDegree, weight_nonDisplacement_eq_totalJetDegree] using hQ

/-- Every individual non-`T` variable needs only the total-jet sampling budget. -/
theorem degreeOf_unscaledLocalSubstitution_nonDisplacement
    (center received : R) (Q : DifferentialPolynomial R d)
    (hQ : ∀ u ∈ Q.support, totalJetDegree u ≤ B) (v : Option (Fin d)) :
    (unscaledLocalSubstitution d center received Q).degreeOf (some v) ≤ B := by
  rw [degreeOf_le_iff]
  intro e he
  exact (Finsupp.le_weight nonDisplacementWeight (by exact Nat.one_ne_zero) e).trans
    (mem_restrictWeightedDegree.mp
      (unscaledLocalSubstitution_mem_nonDisplacement center received Q hQ) e he)

/-- The untruncated displacement degree is at most the ambient differential-weight budget. -/
theorem degreeOf_unscaledLocalSubstitution_T (hd : d < D)
    (center received : R) (Q : DifferentialPolynomial R d)
    (hQ : Q ∈ restrictWeightedDegree (R := R)
      (fun v ↦ match v with | none => 1 | some j => D - j.val) B) :
    (unscaledLocalSubstitution d center received Q).degreeOf (localT d) ≤ B := by
  rw [degreeOf_le_iff]
  intro e he
  exact (Finsupp.le_weight (localContactWeight d) (by exact Nat.one_ne_zero) e).trans
    (mem_restrictWeightedDegree.mp
      (unscaledLocalSubstitution_mem_differentialFormula hd hQ) e he)

/-- A band cutoff at most `D*B` supplies the combined jet budget required by local sampling. -/
theorem totalJetDegree_le_of_band_support {m W Cmin Cmax : ℕ} {L : ℝ}
    (hD : 0 < D) (hL : L ≤ (D : ℝ) * B) (Q : DifferentialPolynomial R d)
    (hQ : Q ∈ asymmetricBandSpace R D d m W Cmin Cmax L hD) :
    ∀ u ∈ Q.support, totalJetDegree u ≤ B := by
  intro u hu
  have ht := totalJetDegree_lt_of_asymmetricBandEligible hD
    (mem_asymmetricBandSpace_iff.mp hQ u hu)
  have hquot : L / D ≤ B := (div_le_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
    (by simpa only [mul_comm] using hL)
  exact_mod_cast ht.le.trans hquot

/-- The optimized band's local error and visible-jet degrees are all at most `2m`.
In particular, the non-displacement grids need not grow with `n`. -/
theorem degreeOf_unscaledLocalSubstitution_band_nonDisplacement
    {m W Cmin Cmax : ℕ} {L : ℝ} (hD : 0 < D) (hL : L ≤ (D : ℝ) * (2 * m))
    (center received : R) (Q : DifferentialPolynomial R d)
    (hQ : Q ∈ asymmetricBandSpace R D d m W Cmin Cmax L hD) (v : Option (Fin d)) :
    (unscaledLocalSubstitution d center received Q).degreeOf (some v) ≤ 2 * m :=
  degreeOf_unscaledLocalSubstitution_nonDisplacement center received Q
    (totalJetDegree_le_of_band_support hD (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hL)
      Q hQ) v

end
end ReedSolomon.HiddenDerivative
