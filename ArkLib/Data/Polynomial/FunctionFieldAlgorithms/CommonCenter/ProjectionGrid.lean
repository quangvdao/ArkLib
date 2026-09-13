/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.ProjectionBounds
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Bounded-grid reduction for projection existence

The checker is complete for its semantic conditions. A polynomial of degree at most `2B`
cannot vanish at every integer in the search grid when the characteristic exceeds `2B`.
Together these reduce search existence to constructing a nonzero bad-slope polynomial with
that degree bound. Constructing it from reducedness and the two partial derivatives is the
remaining geometric obligation; this module does not assume or claim its existence.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.Projection

open CompPoly CPolynomial CPoly

variable {K : Type*} [Field K] [BEq K] [LawfulBEq K]

/-- The executed derivative test is also complete for mathematical coprimality. -/
theorem derivativeCoprime_complete (h : CBivariate K)
    (hc : IsCoprime (RegularCenterObstruction.functionFieldPolynomial h)
      (RegularCenterObstruction.functionFieldPolynomial h).derivative) :
    derivativeCoprime h = true := by
  classical
  apply beq_iff_eq.mpr
  apply FunctionFieldEuclid.value_injective
  rw [FunctionFieldEuclid.value_gcd]
  have hd : FunctionFieldEuclid.value (ClearDenominators.embed h).derivative =
      (FunctionFieldEuclid.value (ClearDenominators.embed h)).derivative := by
    simp [FunctionFieldEuclid.value, CPolynomial.derivative_toPoly,
      Polynomial.derivative_map]
  rw [hd, ClearDenominators.value_embed]
  have hn := normalize_eq_one.mpr (EuclideanDomain.gcd_isUnit_iff.mpr hc)
  simpa [FunctionFieldEuclid.value, CPolynomial.toPoly_one,
    RegularCenterObstruction.functionFieldPolynomial, ClearDenominators.valueGlobal] using hn

/-- Monicity is reflected by both storage conversions. -/
theorem monic_complete (h : CBivariate K) (hm : (CBivariate.toPoly h).Monic) :
    h.monic = true := by
  apply (CPolynomial.monic_toPoly_iff h).mpr
  rw [CBivariate.toPoly_eq_map] at hm
  exact ((CPolynomial.ringEquiv (R := K)).injective.monic_map_iff).mpr hm

/-- Semantic conditions tested by one actual trial. They contain no runtime success premise. -/
structure GoodSlope (Q : CMvPolynomial 2 K) (slope : K) : Prop where
  /-- The scalar normalization produced a monic equation. -/
  monic : (CBivariate.toPoly (normalized slope Q)).Monic
  /-- The equation depends on the fiber coordinate. -/
  positive : 0 < (normalized slope Q).natDegree
  /-- Its derivative is coprime over the rational function field. -/
  coprime : IsCoprime (RegularCenterObstruction.functionFieldPolynomial (normalized slope Q))
    (RegularCenterObstruction.functionFieldPolynomial (normalized slope Q)).derivative
  /-- The normalization scalar does not erase the input. -/
  scale_ne_zero : scale slope Q ≠ 0

/-- No mathematically valid trial is lost by the executable tests. -/
theorem trySlope_isSome_iff (Q : CMvPolynomial 2 K) (slope : K) :
    (trySlope slope Q).isSome ↔ GoodSlope Q slope := by
  constructor
  · intro hs
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
    have h := trySlope_sound slope Q c hc
    have he : c.slope = slope := trySlope_slope slope Q c hc
    have hq : c.equation = normalized slope Q := by simpa [he] using h.equation_eq
    exact ⟨by simpa [hq] using h.monic, by simpa [hq] using h.positive,
      by simpa [hq, Polynomial.separable_def] using h.separable,
      by simpa [h.scale_eq, he] using h.scale_ne_zero⟩
  · intro h
    have hm := monic_complete _ h.monic
    have hc := derivativeCoprime_complete _ h.coprime
    simp [trySlope, hm, hc, h.positive, h.scale_ne_zero]

/-- The zero trial leaves the stored coordinates unchanged. -/
theorem shear_zero (Q : CMvPolynomial 2 K) : shearHom 0 Q = Q := by
  apply fromCMvPolynomial_injective
  rw [shear_semantics]
  have hid : semanticShear (0 : K) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [semanticShear]
    · intro i
      fin_cases i <;> simp [semanticShear]
  rw [hid, RingHom.id_apply]

/-- A stored monic ordinary equation needs no scalar adjustment at slope zero. -/
theorem normalized_zero_monic (h : CBivariate K) (hm : (CBivariate.toPoly h).Monic) :
    normalized 0 (CBivariate.toOrdinaryCMv h) = h := by
  classical
  have ht : transformed 0 (CBivariate.toOrdinaryCMv h) = h := by
    rw [transformed, shear_zero]
    exact BivariateReducedSupport.fromOrdinaryCMv_toOrdinaryCMv h
  have hl : h.leadingCoeff = 1 := by
    apply CPolynomial.toPoly_injective
    rw [show h.leadingCoeff.toPoly = (CBivariate.toPoly h).leadingCoeff by
      simpa [CBivariate.leadingCoeffY] using CBivariate.leadingCoeffY_toPoly h]
    rw [hm, CPolynomial.toPoly_one]
  have hs : scale 0 (CBivariate.toOrdinaryCMv h) = 1 := by
    simp [scale, ht, hl, CPolynomial.coeff_one]
  apply CBivariate.ringEquiv.injective
  change CBivariate.toPoly (normalized 0 (CBivariate.toOrdinaryCMv h)) = CBivariate.toPoly h
  rw [normalized_toPoly, hs, ht]
  simp

/-- Monic positive-degree separable inputs already succeed at the first grid point.
This special case requires no lower bound on the characteristic. -/
theorem hasPassingSlope_of_monic (B : ℕ) (h : CBivariate K)
    (hm : (CBivariate.toPoly h).Monic) (hd : 0 < h.natDegree)
    (hc : IsCoprime (RegularCenterObstruction.functionFieldPolynomial h)
      (RegularCenterObstruction.functionFieldPolynomial h).derivative) :
    HasPassingSlope B (CBivariate.toOrdinaryCMv h) := by
  classical
  refine ⟨0, Nat.zero_le _, (trySlope_isSome_iff _ _).mpr ?_⟩
  have he := normalized_zero_monic h hm
  refine ⟨by simpa only [Nat.cast_zero, he] using hm,
    by simpa only [Nat.cast_zero, he] using hd,
    by simpa only [Nat.cast_zero, he] using hc, ?_⟩
  intro hz
  have hez : normalized 0 (CBivariate.toOrdinaryCMv h) = 0 := by
    apply CBivariate.ringEquiv.injective
    change CBivariate.toPoly (normalized 0 (CBivariate.toOrdinaryCMv h)) = CBivariate.toPoly 0
    rw [normalized_toPoly]
    have hz' : scale 0 (CBivariate.toOrdinaryCMv h) = 0 := by
      simpa only [Nat.cast_zero] using hz
    simp [hz', CBivariate.toPoly_zero]
  have hh : h = 0 := he.symm.trans hez
  exact hm.ne_zero (by rw [hh, CBivariate.toPoly_zero])

omit [BEq K] [LawfulBEq K] in
/-- Root counting on the actual integer grid; only `2B < p` is required for distinctness. -/
theorem exists_grid_nonroot (p B : ℕ) [CharP K p] (hp : 2 * B < p)
    (bad : Polynomial K) (hne : bad ≠ 0) (hdeg : bad.natDegree ≤ 2 * B) :
    ∃ i : ℕ, i ≤ 2 * B ∧ bad.eval (i : K) ≠ 0 := by
  classical
  by_contra h
  apply hne
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero bad
    (f := fun i : Fin (2 * B + 1) => (i.val : K))
  · intro i j hij
    apply Fin.ext
    exact CharP.natCast_injOn_Iio K p (by change i.val < p; have := i.isLt; omega)
      (by change j.val < p; have := j.isLt; omega) hij
  · intro i
    by_contra hi
    exact h ⟨i.val, by have := i.isLt; omega, hi⟩
  · simpa using Nat.lt_succ_of_le hdeg

/-- Exact missing geometric data: a bounded nonzero polynomial containing every bad slope.
The appendix constructs it from the top homogeneous part and irreducible-factor partials;
that construction and its degree estimate have not yet been formalized. -/
structure BadSlopeControl (B : ℕ) (Q : CMvPolynomial 2 K) where
  /-- Polynomial in the shear parameter, not in either curve coordinate. -/
  polynomial : Polynomial K
  /-- The bad directions do not fill the parameter line. -/
  nonzero : polynomial ≠ 0
  /-- At most `2B` grid points can be bad. -/
  degree_le : polynomial.natDegree ≤ 2 * B
  /-- Every direction away from the zero set meets the semantic checker conditions. -/
  good : ∀ slope, polynomial.eval slope ≠ 0 → GoodSlope Q slope

/-- Once the geometric bad-slope control is constructed, the existing search must succeed. -/
theorem hasPassingSlope_of_control (p B : ℕ) [CharP K p] (hp : 2 * B < p)
    (Q : CMvPolynomial 2 K) (control : BadSlopeControl B Q) : HasPassingSlope B Q := by
  obtain ⟨i, hi, hn⟩ := exists_grid_nonroot p B hp control.polynomial
    control.nonzero control.degree_le
  exact ⟨i, hi, (trySlope_isSome_iff Q (i : K)).mpr (control.good _ hn)⟩

end Polynomial.FunctionFieldAlgorithms.CommonCenter.Projection
