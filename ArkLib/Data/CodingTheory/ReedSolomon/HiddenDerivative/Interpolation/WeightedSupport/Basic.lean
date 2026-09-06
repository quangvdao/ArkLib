/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.DimensionBridge
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Lower-cutoff weighted interpolation support

The support retains a minimum number of higher-derivative factors and bounds their weighted
sum. A strict total cutoff supplies all upper bounds, including finiteness; no separate cap
on the first derivative or upper edge on the higher-derivative degree is needed.

The parameter `L` measures the coarse specialization budget `x + D * totalJetDegree`.
In the capacity construction it is `m * D * (1 + g)`. Positive `D` bounds ordinary degree
by this budget, giving finite coefficient coordinates over any field.
-/

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential

noncomputable section

variable {F : Type*} {d D W Cmin : ℕ} {L : ℝ}

/-- The paper's lower-cutoff support, with all upper bounds supplied by the total cutoff. -/
def WeightedSupportEligible (D d W Cmin : ℕ) (L : ℝ)
    (u : JetVariable d →₀ ℕ) : Prop :=
  fullHigherJetWeight u ≤ W ∧ Cmin ≤ fullHigherJetDegree u ∧
    (u none + D * totalJetDegree u : ℕ) < L

/-- A positive coarse weight bounds ordinary degree, even if some jet weights vanish. -/
theorem degree_lt_ceil_of_weightedSupportEligible (hD : 0 < D)
    {u : JetVariable d →₀ ℕ} (hu : WeightedSupportEligible D d W Cmin L u) :
    Finsupp.degree u < ⌈L⌉₊ := by
  rw [exponentDegree_eq_x_add_totalJetDegree]
  have hmul : totalJetDegree u ≤ D * totalJetDegree u := by
    simpa using Nat.mul_le_mul_right (totalJetDegree u) hD
  exact (Nat.add_le_add_left hmul _).trans_lt (Nat.lt_ceil.mpr hu.2.2)

/-- The total cutoff makes the support finite without additional exponent caps. -/
theorem weightedSupportEligible_finite (hD : 0 < D) :
    {u : JetVariable d →₀ ℕ | WeightedSupportEligible D d W Cmin L u}.Finite := by
  apply (Finsupp.finite_of_degree_le ⌈L⌉₊).subset
  intro u hu
  exact (degree_lt_ceil_of_weightedSupportEligible hD hu).le

/-- Finite monomial coordinates satisfying the lower-cutoff inequalities. -/
def weightedSupportExponents (D d W Cmin : ℕ) (L : ℝ) (hD : 0 < D) :
    Finset (JetVariable d →₀ ℕ) :=
  (weightedSupportEligible_finite (d := d) (W := W) (Cmin := Cmin) (L := L) hD).toFinset

@[simp]
theorem mem_weightedSupportExponents {hD : 0 < D} {u : JetVariable d →₀ ℕ} :
    u ∈ weightedSupportExponents D d W Cmin L hD ↔
      WeightedSupportEligible D d W Cmin L u := by
  simp [weightedSupportExponents]

/-- Differential polynomials with exactly the permitted monomial support. -/
def weightedSupportSpace (F : Type*) [CommSemiring F]
    (D d W Cmin : ℕ) (L : ℝ) (hD : 0 < D) :
    Submodule F (DifferentialPolynomial F d) :=
  MvPolynomial.restrictSupport F
    (↑(weightedSupportExponents D d W Cmin L hD) : Set (JetVariable d →₀ ℕ))

/-- Space membership tests each nonzero monomial against the three support inequalities. -/
theorem mem_weightedSupportSpace_iff [CommSemiring F] {hD : 0 < D}
    {Q : DifferentialPolynomial F d} :
    Q ∈ weightedSupportSpace F D d W Cmin L hD ↔
      ∀ u ∈ Q.support, WeightedSupportEligible D d W Cmin L u := by
  rw [weightedSupportSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_weightedSupportExponents]

/-- The total jet degree retains the full coarse denominator `D`. -/
theorem totalJetDegree_lt_of_weightedSupportEligible (hD : 0 < D)
    {u : JetVariable d →₀ ℕ} (hu : WeightedSupportEligible D d W Cmin L u) :
    (totalJetDegree u : ℝ) < L / D := by
  apply (lt_div_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
  have hx : (0 : ℝ) ≤ u none := Nat.cast_nonneg _
  have hweight := hu.2.2
  push_cast at hweight
  nlinarith

/-- Canonical monomial basis for the finite support. -/
def weightedSupportBasis [CommSemiring F] (hD : 0 < D) :=
  MvPolynomial.basisRestrictSupport (R := F)
    (↑(weightedSupportExponents D d W Cmin L hD) : Set (JetVariable d →₀ ℕ))

/-- The number of permitted monomials is exactly the dimension over every field. -/
theorem finrank_weightedSupportSpace_eq_card [Field F] (hD : 0 < D) :
    Module.finrank F (weightedSupportSpace F D d W Cmin L hD) =
      (weightedSupportExponents D d W Cmin L hD).card := by
  unfold weightedSupportSpace
  rw [Module.finrank_eq_card_basis
    (weightedSupportBasis (F := F) (d := d) (W := W) (Cmin := Cmin) (L := L) hD)]
  exact Fintype.card_coe _

/-- The total cutoff supplies any ambient first-derivative cap large enough for that cutoff.
This is an inclusion into a search space, not an additional restriction on the support. -/
theorem weightedSupportSpace_le_exactInterpolationSpace [CommSemiring F]
    {A m M : ℕ} (hD : 0 < D) (hdD : d < D)
    (hL : L ≤ (m * A : ℕ)) (hcap : L ≤ (D : ℝ) * M) :
    weightedSupportSpace F D d W Cmin L hD ≤
      exactInterpolationSpace F D A d m M W hdD := by
  intro Q hQ
  rw [mem_exactInterpolationSpace_iff]
  intro u hu
  have he := mem_weightedSupportSpace_iff.mp hQ u hu
  refine ⟨?_, he.1, ?_⟩
  · have ht := totalJetDegree_lt_of_weightedSupportEligible hD he
    have hquot : L / D ≤ M :=
      (div_le_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
        (by simpa only [mul_comm] using hcap)
    have htotal : totalJetDegree u ≤ M := by exact_mod_cast ht.le.trans hquot
    exact (firstJetExponent_le_totalJetDegree u).trans htotal
  · have hcoarse : u none + D * totalJetDegree u < m * A := by
      exact_mod_cast he.2.2.trans_le hL
    exact (exactInterpolationMonomialWeight_le_coarse D u).trans_lt hcoarse

/-- A cutoff at `D * t` bounds the total jet degree by `t - 1`, with the strict endpoint
preserved. For capacity the parameter `t` is `2 * m`. -/
theorem totalJetDegree_le_pred_of_weightedSupportEligible (hD : 0 < D)
    {t : ℕ} (hL : L ≤ (D : ℝ) * t)
    {u : JetVariable d →₀ ℕ} (hu : WeightedSupportEligible D d W Cmin L u) :
    totalJetDegree u ≤ t - 1 := by
  have ht := totalJetDegree_lt_of_weightedSupportEligible hD hu
  have hquot : L / D ≤ t :=
    (div_le_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
      (by simpa only [mul_comm] using hL)
  have : totalJetDegree u < t := by exact_mod_cast ht.trans_le hquot
  omega

/-- Each supported monomial obeys the exact differential weight budget. -/
theorem exactInterpolationMonomialWeight_lt_of_weightedSupportEligible
    {B : ℕ} (hL : L ≤ B)
    {u : JetVariable d →₀ ℕ} (hu : WeightedSupportEligible D d W Cmin L u) :
    exactInterpolationMonomialWeight D u < B := by
  have hcoarse : u none + D * totalJetDegree u < B := by
    exact_mod_cast hu.2.2.trans_le hL
  exact (exactInterpolationMonomialWeight_le_coarse D u).trans_lt hcoarse

/-- The monomial cutoff controls the polynomial's differential weighted degree.
Positive budget also covers the zero polynomial. -/
theorem differentialWeightedDegree_lt_of_mem_weightedSupportSpace [CommSemiring F]
    {B : ℕ} {hD : 0 < D} (hB : 0 < B) (hL : L ≤ B)
    {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ weightedSupportSpace F D d W Cmin L hD) :
    differentialWeightedDegree D Q < B := by
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_lt_iff hB]
  intro u hu
  exact exactInterpolationMonomialWeight_lt_of_weightedSupportEligible hL
    (mem_weightedSupportSpace_iff.mp hQ u hu)

end
end ReedSolomon.HiddenDerivative
