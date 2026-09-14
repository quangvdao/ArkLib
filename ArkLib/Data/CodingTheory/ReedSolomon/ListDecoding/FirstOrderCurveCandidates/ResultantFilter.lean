/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ChartContract
public import ArkLib.Data.Polynomial.NormProducts.MultiplicationMatrix
public import CompPoly.Univariate.EuclideanAlgorithm
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import ArkLib.ToMathlib.Polynomial.NormResultant

/-!
# Characteristic-polynomial coefficient filter

For each residual this module computes the stored determinant `det(W I - m_g)` in the
monomial quotient basis. This is the characteristic-polynomial form of the paper's resultant
filter. The formal bridges below identify the computed polynomial with both the matrix
characteristic polynomial and the Sylvester resultant, including nonreduced monic quotients.
The coefficient scan counts neither factors nor multiplicities: it selects the first nonzero
coefficient in increasing powers of `W` and normalizes that polynomial in `u`.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates

open CompPoly

variable {E : Type} [Field E] [BEq E] [LawfulBEq E]

/-- Compute the characteristic polynomial of multiplication by one residual, with `W` outermost.
The quotient interpretation requires a monic fiber; the determinant itself is always defined. -/
def characteristicPolynomial (h g : CPolynomial (CPolynomial E)) :
    CPolynomial (CPolynomial E) :=
  let m := CPolynomial.NormProducts.multiplicationMatrix h.natDegree h g
  Matrix.det (fun i j : Fin h.natDegree =>
    (if i = j then CPolynomial.X else 0) - CPolynomial.C (m i j))

/-- The stored computation refines the matrix characteristic polynomial exactly. -/
theorem characteristicPolynomial_toPoly (h g : CPolynomial (CPolynomial E)) :
    (characteristicPolynomial h g).toPoly =
      (CPolynomial.NormProducts.multiplicationMatrix h.natDegree h g).charpoly := by
  unfold characteristicPolynomial
  dsimp only
  rw [← CPolynomial.toPolyRingHom_apply]
  erw [RingHom.map_det]
  unfold Matrix.charpoly
  apply congrArg Matrix.det
  funext i j
  erw [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [CPolynomial.toPolyRingHom_apply]
  by_cases hij : i = j <;>
    simp [hij, CPolynomial.toPoly_sub, CPolynomial.toPoly_neg,
      CPolynomial.C_toPoly, CPolynomial.X_toPoly]

/-- The computed characteristic polynomial is exactly `Res_V(h, W - g)`. The coefficient
ring is the polynomial ring in the projection parameter, and the fiber may be nonreduced. -/
theorem characteristicPolynomial_eq_resultant (h g : CPolynomial (CPolynomial E))
    (hh : h.monic) :
    (characteristicPolynomial h g).toPoly =
      Polynomial.resultant (h.toPoly.map Polynomial.C)
        (Polynomial.C Polynomial.X - g.toPoly.map Polynomial.C) := by
  let : IsDomain (CPolynomial E) := CPolynomial.ringEquiv.toMulEquiv.isDomain
  rw [characteristicPolynomial_toPoly, CPolynomial.natDegree_toPoly]
  have hm : CPolynomial.NormProducts.multiplicationMatrix h.toPoly.natDegree h g =
      fun i j : Fin h.toPoly.natDegree =>
        ((g.toPoly * Polynomial.X ^ j.val) %ₘ h.toPoly).coeff i.val := by
    funext i j
    exact CPolynomial.NormProducts.multiplicationMatrix_apply _ h g hh i j
  rw [hm]
  exact Polynomial.charpoly_modByMonic_eq_resultant h.toPoly g.toPoly
    ((CPolynomial.monic_toPoly_iff h).mp hh)

/-- Monicity supplies a nonzero coefficient even for a universally vanishing residual. -/
theorem characteristicPolynomial_monic (h g : CPolynomial (CPolynomial E)) :
    (characteristicPolynomial h g).monic := by
  rw [CPolynomial.monic_toPoly_iff, characteristicPolynomial_toPoly]
  exact Matrix.charpoly_monic _

/-- A residual zero on the whole stored curve has characteristic polynomial `W^b`. -/
theorem characteristicPolynomial_zero (h : CPolynomial (CPolynomial E)) (hh : h.monic) :
    characteristicPolynomial h 0 = CPolynomial.X ^ h.natDegree := by
  apply CPolynomial.toPoly_injective
  rw [characteristicPolynomial_toPoly, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
  have hz : CPolynomial.NormProducts.multiplicationMatrix h.natDegree h 0 = 0 := by
    funext i j
    rw [CPolynomial.NormProducts.multiplicationMatrix_apply _ _ _ hh]
    simp [CPolynomial.toPoly_zero]
  rw [hz, Matrix.charpoly_zero]
  simp

/-- Scan the stored polynomial in increasing powers of `W`. -/
def lowestCoefficient? (chi : CPolynomial (CPolynomial E)) : Option (CPolynomial E) :=
  ((List.range (chi.natDegree + 1)).map chi.coeff).find? fun c => c != 0

/-- Every successful scan returns a nonzero coefficient. -/
theorem lowestCoefficient?_ne_zero (chi : CPolynomial (CPolynomial E))
    (c : CPolynomial E) (hc : lowestCoefficient? chi = some c) : c ≠ 0 := by
  simpa using List.find?_some hc

omit [LawfulBEq E] in
/-- The selected value is an actual coefficient within the degree bound. -/
theorem lowestCoefficient?_is_coefficient (chi : CPolynomial (CPolynomial E))
    (c : CPolynomial E) (hc : lowestCoefficient? chi = some c) :
    ∃ j ≤ chi.natDegree, chi.coeff j = c := by
  obtain ⟨j, hj, heq⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hc)
  exact ⟨j, by simpa using hj, heq⟩

/-- The executable scan returns exactly the first nonzero coefficient, with its index. -/
theorem lowestCoefficient?_eq_some_iff (chi : CPolynomial (CPolynomial E))
    (c : CPolynomial E) :
    lowestCoefficient? chi = some c ↔ c ≠ 0 ∧
      ∃ j ≤ chi.natDegree, chi.coeff j = c ∧ ∀ i < j, chi.coeff i = 0 := by
  simp only [lowestCoefficient?, List.find?_eq_some_iff_getElem]
  simp
  aesop

/-- The indexed scan gives the exact generic order in `W`. -/
theorem lowestCoefficient?_order (chi : CPolynomial (CPolynomial E))
    (c : CPolynomial E) (hc : lowestCoefficient? chi = some c) :
    ∃ j ≤ chi.natDegree, chi.coeff j = c ∧ Polynomial.X ^ j ∣ chi.toPoly ∧
      ¬Polynomial.X ^ (j + 1) ∣ chi.toPoly := by
  obtain ⟨hn, j, hj, hjc, hbefore⟩ := (lowestCoefficient?_eq_some_iff chi c).mp hc
  refine ⟨j, hj, hjc, ?_, ?_⟩
  · rw [Polynomial.X_pow_dvd_iff]
    intro i hi
    rw [← CPolynomial.coeff_toPoly, hbefore i hi]
  · intro h
    have hz := Polynomial.X_pow_dvd_iff.mp h j (by omega)
    rw [← CPolynomial.coeff_toPoly, hjc] at hz
    exact hn hz

/-- At the first generic nonzero coefficient, specialization raises the order in `W`
exactly when that coefficient vanishes. This holds for arbitrary ring specializations. -/
theorem lowestCoefficient?_specialization_iff {K : Type*} [CommRing K]
    (σ : CPolynomial E →+* K) (chi : CPolynomial (CPolynomial E))
    (c : CPolynomial E) (hc : lowestCoefficient? chi = some c) :
    ∃ j ≤ chi.natDegree, chi.coeff j = c ∧ (∀ i < j, chi.coeff i = 0) ∧
      (Polynomial.X ^ (j + 1) ∣ chi.toPoly.map σ ↔ σ c = 0) := by
  obtain ⟨_, j, hj, hjc, hbefore⟩ := (lowestCoefficient?_eq_some_iff chi c).mp hc
  refine ⟨j, hj, hjc, hbefore, ?_⟩
  rw [Polynomial.X_pow_dvd_iff]
  constructor
  · intro h
    simpa only [Polynomial.coeff_map, ← CPolynomial.coeff_toPoly, hjc] using h j (by omega)
  · intro hz i hi
    rw [Polynomial.coeff_map, ← CPolynomial.coeff_toPoly]
    by_cases hij : i = j
    · simpa only [hij, hjc] using hz
    · rw [hbefore i (by omega), map_zero]

/-- A monic polynomial always supplies a coefficient to the scan. -/
theorem lowestCoefficient?_exists (chi : CPolynomial (CPolynomial E)) (hm : chi.monic) :
    ∃ c, lowestCoefficient? chi = some c ∧ c ≠ 0 := by
  cases hs : lowestCoefficient? chi with
  | some c => exact ⟨c, rfl, lowestCoefficient?_ne_zero chi c hs⟩
  | none =>
    have hnone := List.find?_eq_none.mp hs
    have hmem : chi.coeff chi.natDegree ∈
        (List.range (chi.natDegree + 1)).map chi.coeff :=
      List.mem_map.mpr ⟨chi.natDegree, by simp, rfl⟩
    have hzero : chi.coeff chi.natDegree = 0 := by
      simpa using hnone _ hmem
    have hone : chi.coeff chi.natDegree = 1 := by
      rw [CPolynomial.coeff_toPoly, CPolynomial.natDegree_toPoly]
      exact ((CPolynomial.monic_toPoly_iff chi).mp hm).coeff_natDegree
    exact False.elim (one_ne_zero (hone.symm.trans hzero))

/-- Normalize the selected coefficient in the projection variable. -/
def normalizedLowestCoefficient? (chi : CPolynomial (CPolynomial E)) :
    Option (CPolynomial E) :=
  (lowestCoefficient? chi).map CPolynomial.monicNormalize

/-- The per-position polynomial filter; no products across received positions are formed. -/
def residualFilter? (h g : CPolynomial (CPolynomial E)) : Option (CPolynomial E) :=
  normalizedLowestCoefficient? (characteristicPolynomial h g)

/-- Monic normalization changes a coefficient by a unit and hence preserves its roots over
every extension field. -/
theorem monicNormalize_eval₂_eq_zero_iff {K : Type*} [Field K]
    (phi : E →+* K) (u : K) (c : CPolynomial E) :
    c.monicNormalize.toPoly.eval₂ phi u = 0 ↔ c.toPoly.eval₂ phi u = 0 := by
  classical
  rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
  have hu : IsUnit (Polynomial.eval₂ phi u (normUnit c.toPoly : Polynomial E)) :=
    (normUnit c.toPoly).isUnit.map (Polynomial.eval₂RingHom phi u)
  rw [normalize_apply, Polynomial.eval₂_mul, mul_eq_zero, or_iff_left hu.ne_zero]

/-- The normalized filter detects precisely an increase beyond the first generic nonzero
`W`-coefficient. The order-increase hypothesis remains explicit; this theorem does not claim
that a geometric component forces such an increase. -/
theorem residualFilter?_specialization_iff {K : Type*} [Field K]
    (phi : E →+* K) (u : K) (h g : CPolynomial (CPolynomial E))
    (c : CPolynomial E) (hc : residualFilter? h g = some c) :
    ∃ j ≤ (characteristicPolynomial h g).natDegree,
      (characteristicPolynomial h g).coeff j ≠ 0 ∧
      c = ((characteristicPolynomial h g).coeff j).monicNormalize ∧
      (∀ i < j, (characteristicPolynomial h g).coeff i = 0) ∧
      (Polynomial.X ^ (j + 1) ∣ (characteristicPolynomial h g).toPoly.map
        ((Polynomial.eval₂RingHom phi u).comp CPolynomial.toPolyRingHom) ↔
        c.toPoly.eval₂ phi u = 0) := by
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨j, hj, hja, hbefore, hiff⟩ := lowestCoefficient?_specialization_iff
    ((Polynomial.eval₂RingHom phi u).comp CPolynomial.toPolyRingHom)
      (characteristicPolynomial h g) a ha
  refine ⟨j, hj, ?_, ?_, hbefore, ?_⟩
  · rw [hja]
    exact lowestCoefficient?_ne_zero _ _ ha
  · rw [hja]
  · rw [monicNormalize_eval₂_eq_zero_iff]
    simpa only [RingHom.comp_apply, CPolynomial.toPolyRingHom_apply,
      Polynomial.coe_eval₂RingHom] using hiff

/-- For monic fibers the same order-increase criterion applies to the exact Sylvester
resultant `Res_V(h, W - g)`. No reducedness or separability assumption is used. -/
theorem residualFilter?_resultant_specialization_iff {K : Type*} [Field K]
    (phi : E →+* K) (u : K) (h g : CPolynomial (CPolynomial E)) (hh : h.monic)
    (c : CPolynomial E) (hc : residualFilter? h g = some c) :
    ∃ j ≤ (characteristicPolynomial h g).natDegree,
      (characteristicPolynomial h g).coeff j ≠ 0 ∧
      c = ((characteristicPolynomial h g).coeff j).monicNormalize ∧
      (∀ i < j, (characteristicPolynomial h g).coeff i = 0) ∧
      (Polynomial.X ^ (j + 1) ∣
        (Polynomial.resultant (h.toPoly.map Polynomial.C)
          (Polynomial.C Polynomial.X - g.toPoly.map Polynomial.C)).map
            ((Polynomial.eval₂RingHom phi u).comp CPolynomial.toPolyRingHom) ↔
        c.toPoly.eval₂ phi u = 0) := by
  obtain ⟨j, hj, hn, hcj, hbefore, hiff⟩ := residualFilter?_specialization_iff phi u h g c hc
  refine ⟨j, hj, hn, hcj, hbefore, ?_⟩
  rwa [characteristicPolynomial_eq_resultant h g hh] at hiff

/-- The determinant scan cannot fail: its characteristic polynomial is monic. -/
theorem residualFilter?_exists (h g : CPolynomial (CPolynomial E)) :
    ∃ c, residualFilter? h g = some c := by
  obtain ⟨c, hc, _⟩ := lowestCoefficient?_exists (characteristicPolynomial h g)
    (characteristicPolynomial_monic h g)
  exact ⟨CPolynomial.monicNormalize c, by
    simp [residualFilter?, normalizedLowestCoefficient?, hc]⟩

/-- Every selected normalized coefficient is monic, and hence nonzero. -/
theorem residualFilter?_monic (h g : CPolynomial (CPolynomial E))
    (c : CPolynomial E) (hc : residualFilter? h g = some c) : c.monic := by
  classical
  obtain ⟨a, ha, hane⟩ := lowestCoefficient?_exists (characteristicPolynomial h g)
    (characteristicPolynomial_monic h g)
  have heq : CPolynomial.monicNormalize a = c := by
    simpa [residualFilter?, normalizedLowestCoefficient?, ha] using hc
  rw [← heq, CPolynomial.monic_toPoly_iff,
    CPolynomial.monicNormalize_toPoly_eq_normalize]
  exact Polynomial.monic_normalize (by
    intro hz
    apply hane
    apply CPolynomial.toPoly_injective
    simpa [CPolynomial.toPoly_zero] using hz)

/-- A whole-curve zero residual contributes the constant polynomial one. -/
theorem residualFilter?_zero (h : CPolynomial (CPolynomial E)) (hh : h.monic) :
    residualFilter? h 0 = some 1 := by
  classical
  obtain ⟨a, ha, hane⟩ := lowestCoefficient?_exists (characteristicPolynomial h 0)
    (characteristicPolynomial_monic h 0)
  obtain ⟨j, _, hj⟩ := lowestCoefficient?_is_coefficient _ a ha
  rw [characteristicPolynomial_zero h hh, CPolynomial.coeff_toPoly,
    CPolynomial.toPoly_pow, CPolynomial.X_toPoly, Polynomial.coeff_X_pow] at hj
  have hone : a = 1 := by
    split at hj
    · exact hj.symm
    · exact False.elim (hane hj.symm)
  rw [hone] at ha
  have hn : CPolynomial.monicNormalize (1 : CPolynomial E) = 1 := by
    apply CPolynomial.toPoly_injective
    rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
    simp [CPolynomial.toPoly_one]
  simp [residualFilter?, normalizedLowestCoefficient?, ha, hn]

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates
