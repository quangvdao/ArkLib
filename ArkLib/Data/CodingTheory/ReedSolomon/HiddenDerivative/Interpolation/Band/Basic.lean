/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.DimensionBridge
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Coordinates


/-!
# Finite asymmetric-band interpolation coordinates

This is the separate support of [Dao, Kominers, Thaler, and Zheng,
*Reed--Solomon List Decoding and Mutual Correlated Agreement up to Capacity*][DKTZ26],
Theorem 3.4 (`thm:asymmetric-band`), equations (22)–(23)
(`eq:band-support` and `eq:band-space`).

The strict real threshold `L` is intended to be `m * D * (1 + g)`. All jets are charged by
`D`, and the higher-jet degree has both lower and upper edges. This support is separate from
the cap-free derivative-weighted index. The structural results need only `D > 0`; the
coordinate split additionally needs `d > 0`. No numerical parameter certificate or local-rank
bound is asserted here. The real threshold and proof-facing support are noncomputable.
-/

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

variable {F : Type*} {d D m W Cmin Cmax : ℕ} {L : ℝ}

/-- The higher-jet lattice points between the two ordinary-degree edges. -/
def asymmetricBandTuples (d W Cmin Cmax : ℕ) : Finset (HigherJetTuple d) :=
  (weightedHigherJetTuples d W).filter fun c ↦
    Cmin ≤ higherJetTupleDegree c ∧ higherJetTupleDegree c ≤ Cmax

@[simp]
theorem mem_asymmetricBandTuples {c : HigherJetTuple d} :
    c ∈ asymmetricBandTuples d W Cmin Cmax ↔
      higherJetTupleWeight c ≤ W ∧
        Cmin ≤ higherJetTupleDegree c ∧ higherJetTupleDegree c ≤ Cmax := by
  simp [asymmetricBandTuples]

/-- Full monomial support of the asymmetric band, with the paper's strict real cutoff. -/
def AsymmetricBandEligible (D d m W Cmin Cmax : ℕ) (L : ℝ)
    (u : JetVariable d →₀ ℕ) : Prop :=
  firstJetExponent u ≤ m ∧ fullHigherJetWeight u ≤ W ∧
    Cmin ≤ fullHigherJetDegree u ∧ fullHigherJetDegree u ≤ Cmax ∧
      (u none + D * totalJetDegree u : ℕ) < L

/-- A real strict cutoff on an integer weight is exactly a natural ceiling cutoff.
This includes nonpositive thresholds, when both sides are false. -/
theorem asymmetricBand_weight_lt_iff (u : JetVariable d →₀ ℕ) :
    (u none + D * totalJetDegree u : ℕ) < L ↔
      u none + D * totalJetDegree u < ⌈L⌉₊ :=
  Nat.lt_ceil.symm

/-- Positive coarse jet weight bounds the full ordinary degree of every eligible exponent. -/
theorem degree_lt_ceil_of_asymmetricBandEligible (hD : 0 < D)
    {u : JetVariable d →₀ ℕ} (hu : AsymmetricBandEligible D d m W Cmin Cmax L u) :
    Finsupp.degree u < ⌈L⌉₊ := by
  rw [exponentDegree_eq_x_add_totalJetDegree]
  have hmul : totalJetDegree u ≤ D * totalJetDegree u := by
    simpa using Nat.mul_le_mul_right (totalJetDegree u) hD
  exact (Nat.add_le_add_left hmul _).trans_lt
    ((asymmetricBand_weight_lt_iff u).mp hu.2.2.2.2)

/-- Finiteness uses the positive coarse weight, never the zero high-jet weights. -/
theorem asymmetricBandEligible_finite (hD : 0 < D) :
    {u : JetVariable d →₀ ℕ | AsymmetricBandEligible D d m W Cmin Cmax L u}.Finite := by
  apply (Finsupp.finite_of_degree_le ⌈L⌉₊).subset
  intro u hu
  exact (degree_lt_ceil_of_asymmetricBandEligible hD hu).le

/-- Finite support; `D > 0` is retained explicitly in the API. -/
def asymmetricBandExponents (D d m W Cmin Cmax : ℕ) (L : ℝ) (hD : 0 < D) :
    Finset (JetVariable d →₀ ℕ) :=
  (asymmetricBandEligible_finite (d := d) (m := m) (W := W)
    (Cmin := Cmin) (Cmax := Cmax) (L := L) hD).toFinset

@[simp]
theorem mem_asymmetricBandExponents {hD : 0 < D} {u : JetVariable d →₀ ℕ} :
    u ∈ asymmetricBandExponents D d m W Cmin Cmax L hD ↔
      AsymmetricBandEligible D d m W Cmin Cmax L u := by
  simp [asymmetricBandExponents]

/-- Differential polynomials supported in the asymmetric band. -/
def asymmetricBandSpace (F : Type*) [CommSemiring F]
    (D d m W Cmin Cmax : ℕ) (L : ℝ) (hD : 0 < D) :
    Submodule F (DifferentialPolynomial F d) :=
  MvPolynomial.restrictSupport F
    (↑(asymmetricBandExponents D d m W Cmin Cmax L hD) : Set (JetVariable d →₀ ℕ))

/-- Membership means that each support monomial satisfies the actual band inequalities. -/
theorem mem_asymmetricBandSpace_iff [CommSemiring F] {hD : 0 < D}
    {Q : DifferentialPolynomial F d} :
    Q ∈ asymmetricBandSpace F D d m W Cmin Cmax L hD ↔
      ∀ u ∈ Q.support, AsymmetricBandEligible D d m W Cmin Cmax L u := by
  rw [asymmetricBandSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_asymmetricBandExponents]

/-- Canonical monomial columns of the band space. -/
abbrev AsymmetricBandIndex (D d m W Cmin Cmax : ℕ) (L : ℝ) (hD : 0 < D) :=
  ↥(asymmetricBandExponents D d m W Cmin Cmax L hD)

/-- The monomial basis inherited from finite support. -/
def asymmetricBandBasis [CommSemiring F] (hD : 0 < D) :=
  MvPolynomial.basisRestrictSupport (R := F)
    (↑(asymmetricBandExponents D d m W Cmin Cmax L hD) : Set (JetVariable d →₀ ℕ))

/-- Canonical finite coefficient coordinates for the band space. -/
def asymmetricBandRepr [CommSemiring F] (hD : 0 < D) :
    asymmetricBandSpace F D d m W Cmin Cmax L hD ≃ₗ[F]
      (AsymmetricBandIndex D d m W Cmin Cmax L hD →₀ F) :=
  (asymmetricBandBasis (F := F) (d := d) (m := m) (W := W)
    (Cmin := Cmin) (Cmax := Cmax) (L := L) hD).repr

/-- The canonical coordinates are multivariate polynomial coefficients. -/
@[simp]
theorem asymmetricBandRepr_apply [CommSemiring F] (hD : 0 < D)
    (Q : asymmetricBandSpace F D d m W Cmin Cmax L hD)
    (u : AsymmetricBandIndex D d m W Cmin Cmax L hD) :
    asymmetricBandRepr hD Q u = MvPolynomial.coeff u.1 Q.1 := rfl

/-- Dimension is exactly the number of supported monomials over any field. -/
theorem finrank_asymmetricBandSpace_eq_card [Field F] (hD : 0 < D) :
    Module.finrank F (asymmetricBandSpace F D d m W Cmin Cmax L hD) =
      (asymmetricBandExponents D d m W Cmin Cmax L hD).card := by
  unfold asymmetricBandSpace
  rw [Module.finrank_eq_card_basis
    (asymmetricBandBasis (F := F) (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD)]
  exact Fintype.card_coe _

/-- Total jet degree in the four coordinate groups. -/
theorem totalJetDegree_eq_coordinates (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    totalJetDegree u = (exactExponentCoordinatesEquiv hd u).2.1.1 +
      (exactExponentCoordinatesEquiv hd u).2.1.2 +
        higherJetTupleDegree (exactExponentCoordinatesEquiv hd u).2.2 := by
  rw [totalJetDegree, Finsupp.degree_eq_sum, sum_jet_eq_y₀_add_y₁_add_higher hd]
  simp [higherJetTupleDegree]

/-- Higher-jet degree in the existing coordinate split. -/
theorem fullHigherJetDegree_eq_coordinates (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    fullHigherJetDegree u =
      higherJetTupleDegree (exactExponentCoordinatesEquiv hd u).2.2 := by
  rw [fullHigherJetDegree, Finsupp.weight_eq_sum, sum_jet_eq_y₀_add_y₁_add_higher hd]
  simp [higherJetTupleDegree]

/-- Integer residual budget for `(X,Y₀)` after fixing `Y₁` and the higher jets. -/
def asymmetricBandResidual (D b₁ : ℕ) (L : ℝ) (c : HigherJetTuple d) : ℕ :=
  ⌈L⌉₊ - D * (b₁ + higherJetTupleDegree c)

/-- Coordinate-level eligibility with the exact staircase residual. -/
def AsymmetricBandCoordinatesEligible (D d m W Cmin Cmax : ℕ) (L : ℝ)
    (p : ExactExponentCoordinates d) : Prop :=
  p.2.2 ∈ asymmetricBandTuples d W Cmin Cmax ∧ p.2.1.2 ≤ m ∧
    p.1 + D * p.2.1.1 < asymmetricBandResidual D p.2.1.2 L p.2.2

/-- Exact identification of the paper's support with nested counting coordinates. -/
theorem asymmetricBandEligible_iff_coordinates (hd : 0 < d)
    (u : JetVariable d →₀ ℕ) :
    AsymmetricBandEligible D d m W Cmin Cmax L u ↔
      AsymmetricBandCoordinatesEligible D d m W Cmin Cmax L
        (exactExponentCoordinatesEquiv hd u) := by
  rw [AsymmetricBandEligible, asymmetricBand_weight_lt_iff,
    firstJetExponent_eq_coordinate hd, fullHigherJetWeight_eq_coordinate hd,
    fullHigherJetDegree_eq_coordinates hd, totalJetDegree_eq_coordinates hd]
  simp only [AsymmetricBandCoordinatesEligible, mem_asymmetricBandTuples,
    asymmetricBandResidual, Nat.lt_sub_iff_add_lt, exactExponentCoordinatesEquiv_x]
  simp only [Nat.mul_add, Nat.add_assoc]
  tauto

/-- Finite nested dimension index: band tuple, capped first jet, staircase pair. -/
abbrev AsymmetricBandDimensionIndex (D d m W Cmin Cmax : ℕ) (L : ℝ) :=
  Σ c : ↥(asymmetricBandTuples d W Cmin Cmax),
    Σ b₁ : Fin (m + 1), StaircaseIndex D (asymmetricBandResidual D b₁.val L c.1)

/-- The exact finite dimension sum; there is no approximation or integral bound here. -/
def asymmetricBandDimensionCount (D d m W Cmin Cmax : ℕ) (L : ℝ) : ℕ :=
  ∑ c ∈ asymmetricBandTuples d W Cmin Cmax,
    ∑ b₁ ∈ Finset.range (m + 1), staircaseCount D (asymmetricBandResidual D b₁ L c)

/-- Split eligible coordinates into the finite dependent dimension index. -/
def asymmetricBandCoordinateIndexEquiv (hD : 0 < D) :
    {p : ExactExponentCoordinates d // AsymmetricBandCoordinatesEligible D d m W Cmin Cmax L p} ≃
      AsymmetricBandDimensionIndex D d m W Cmin Cmax L where
  toFun p := ⟨⟨p.1.2.2, p.2.1⟩, ⟨⟨p.1.2.1.2, Nat.lt_succ_of_le p.2.2.1⟩,
    (staircaseIndexEquiv D (asymmetricBandResidual D p.1.2.1.2 L p.1.2.2) hD).symm
      ⟨(p.1.1, p.1.2.1.1), p.2.2.2⟩⟩⟩
  invFun p :=
    let q := staircaseIndexEquiv D (asymmetricBandResidual D p.2.1.val L p.1.1) hD p.2.2
    ⟨(q.1.1, ((q.1.2, p.2.1.val), p.1.1)), ⟨p.1.2, Nat.le_of_lt_succ p.2.1.isLt, q.2⟩⟩
  left_inv p := by
    apply Subtype.ext
    simp [staircaseIndexEquiv]
  right_inv p := by
    rcases p with ⟨c, b₁, q⟩
    simp [staircaseIndexEquiv]

/-- Actual band monomial columns are equivalent to the nested staircase index. -/
def asymmetricBandIndexEquivDimensionIndex (hd : 0 < d) (hD : 0 < D) :
    AsymmetricBandIndex D d m W Cmin Cmax L hD ≃
      AsymmetricBandDimensionIndex D d m W Cmin Cmax L :=
  (Equiv.subtypeEquiv (Equiv.refl _) fun _ ↦ mem_asymmetricBandExponents).trans <|
    (Equiv.subtypeEquiv (exactExponentCoordinatesEquiv hd)
      (asymmetricBandEligible_iff_coordinates hd)).trans <|
        asymmetricBandCoordinateIndexEquiv hD

/-- The finite nested index counts the dimension sum. -/
theorem card_asymmetricBandDimensionIndex :
    Fintype.card (AsymmetricBandDimensionIndex D d m W Cmin Cmax L) =
      asymmetricBandDimensionCount D d m W Cmin Cmax L := by
  rw [Fintype.card_sigma]
  calc
    _ = ∑ c : ↥(asymmetricBandTuples d W Cmin Cmax),
        ∑ b₁ : Fin (m + 1), staircaseCount D (asymmetricBandResidual D b₁.val L c.1) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro b hb
      exact card_staircaseIndex _ _
    _ = ∑ c ∈ asymmetricBandTuples d W Cmin Cmax,
        ∑ b₁ : Fin (m + 1), staircaseCount D (asymmetricBandResidual D b₁.val L c) :=
      Finset.sum_coe_sort (asymmetricBandTuples d W Cmin Cmax)
        (fun c : HigherJetTuple d ↦
          ∑ b₁ : Fin (m + 1), staircaseCount D (asymmetricBandResidual D b₁.val L c))
    _ = asymmetricBandDimensionCount D d m W Cmin Cmax L := by
      apply Finset.sum_congr rfl
      intro c hc
      exact Fin.sum_univ_eq_sum_range
        (fun b₁ ↦ staircaseCount D (asymmetricBandResidual D b₁ L c)) (m + 1)

/-- Exact dimension formula for the asymmetric-band polynomial space. -/
theorem finrank_asymmetricBandSpace_eq_dimensionCount [Field F] (hd : 0 < d) (hD : 0 < D) :
    Module.finrank F (asymmetricBandSpace F D d m W Cmin Cmax L hD) =
      asymmetricBandDimensionCount D d m W Cmin Cmax L := by
  rw [finrank_asymmetricBandSpace_eq_card hD, ← Fintype.card_coe]
  exact (Fintype.card_congr (asymmetricBandIndexEquivDimensionIndex hd hD)).trans
    card_asymmetricBandDimensionIndex

/-- When the real band threshold is at most `mA`, the band embeds in the landed exact space.
The stronger boundary `d < D` is required only by that destination space. -/
theorem asymmetricBandSpace_le_exactInterpolationSpace [CommSemiring F]
    {A : ℕ} (hD : 0 < D) (hdD : d < D) (hL : L ≤ (m * A : ℕ)) :
    asymmetricBandSpace F D d m W Cmin Cmax L hD ≤
      exactInterpolationSpace F D A d m m W hdD := by
  intro Q hQ
  rw [mem_exactInterpolationSpace_iff]
  intro u hu
  have he := mem_asymmetricBandSpace_iff.mp hQ u hu
  refine ⟨he.1, he.2.1, ?_⟩
  have hcoarse : u none + D * totalJetDegree u < m * A := by
    exact_mod_cast he.2.2.2.2.trans_le hL
  exact (exactInterpolationMonomialWeight_le_coarse D u).trans_lt hcoarse

/-- The total jet degree bound keeps the ambient denominator `D` from the manuscript. -/
theorem totalJetDegree_lt_of_asymmetricBandEligible (hD : 0 < D)
    {u : JetVariable d →₀ ℕ} (hu : AsymmetricBandEligible D d m W Cmin Cmax L u) :
    (totalJetDegree u : ℝ) < L / D := by
  apply (lt_div_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
  have hx : (0 : ℝ) ≤ u none := Nat.cast_nonneg _
  have hweight := hu.2.2.2.2
  push_cast at hweight
  nlinarith

/-- The coarse band weight bounds every individual jet degree without losing `D-d` in the
denominator. This is useful when the band cutoff is at most `2*m*D`. -/
theorem jetDegree_le_of_mem_asymmetricBandSpace [CommSemiring F]
    (hD : 0 < D) {t : ℕ} (hL : L ≤ (D : ℝ) * t)
    {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ asymmetricBandSpace F D d m W Cmin Cmax L hD) (j : Fin (d + 1)) :
    jetDegree Q j ≤ t := by
  rw [jetDegree, MvPolynomial.degreeOf_le_iff]
  intro u hu
  have htotal := totalJetDegree_lt_of_asymmetricBandEligible hD
    (mem_asymmetricBandSpace_iff.mp hQ u hu)
  have hcoord : u (some j) ≤ totalJetDegree u := Finsupp.le_degree j u.some
  have hcoord' : (u (some j) : ℝ) ≤ totalJetDegree u := by exact_mod_cast hcoord
  have hquot : L / D ≤ t := (div_le_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
    (by simpa only [mul_comm] using hL)
  exact_mod_cast (hcoord'.trans htotal.le).trans hquot


end
end ReedSolomon.HiddenDerivative
