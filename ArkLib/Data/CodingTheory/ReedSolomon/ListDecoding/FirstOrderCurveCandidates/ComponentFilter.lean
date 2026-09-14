/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ResultantFilter
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ComponentRemoval

/-! # Componentwise interpretation of the direct coefficient filter -/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates

open CompPoly
variable {E : Type} [Field E] [BEq E] [LawfulBEq E]

/-- Characteristic polynomials multiply along a global monic factorization. -/
theorem characteristicPolynomial_mul (d q g : CPolynomial (CPolynomial E))
    (hd : d.monic) (hq : q.monic) :
    characteristicPolynomial (d * q) g =
      characteristicPolynomial d g * characteristicPolynomial q g := by
  have hdm := (CPolynomial.monic_toPoly_iff _).mp hd
  have hqm := (CPolynomial.monic_toPoly_iff _).mp hq
  have hprod : (d * q).monic := (CPolynomial.monic_toPoly_iff _).mpr (by
    rw [CPolynomial.toPoly_mul]; exact hdm.mul hqm)
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.toPoly_mul, characteristicPolynomial_eq_resultant _ _ hprod,
    characteristicPolynomial_eq_resultant _ _ hd, characteristicPolynomial_eq_resultant _ _ hq,
    CPolynomial.toPoly_mul, Polynomial.map_mul]
  have ha := hdm.map (Polynomial.C (R := CPolynomial E))
  have hb := hqm.map (Polynomial.C (R := CPolynomial E))
  rw [ha.natDegree_mul hb]
  exact Polynomial.resultant_mul_left _ _ _ _ le_rfl

/-- A residual divisible by the whole monic factor contributes exactly its degree in `W`. -/
theorem characteristicPolynomial_of_dvd (d g : CPolynomial (CPolynomial E))
    (hd : d.monic) (hg : d.toPoly ∣ g.toPoly) :
    characteristicPolynomial d g = CPolynomial.X ^ d.natDegree := by
  apply CPolynomial.toPoly_injective
  rw [characteristicPolynomial_toPoly, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
  have hz : CPolynomial.NormProducts.multiplicationMatrix d.natDegree d g = 0 := by
    funext i j
    rw [CPolynomial.NormProducts.multiplicationMatrix_apply _ _ _ hd,
      (Polynomial.modByMonic_eq_zero_iff_dvd ((CPolynomial.monic_toPoly_iff _).mp hd)).mpr
        (dvd_mul_of_dvd_left hg _)]
    rfl
  rw [hz, Matrix.charpoly_zero]
  simp

/-- The constant coefficient detects the specialized resultant, retaining nilpotent multiplicity. -/
theorem characteristicPolynomial_coeff_zero_map_iff {K : Type*} [Field K]
    (σ : CPolynomial E →+* K) (h g : CPolynomial (CPolynomial E)) (hh : h.monic) :
    σ ((characteristicPolynomial h g).coeff 0) = 0 ↔
      Polynomial.resultant (h.toPoly.map σ) (g.toPoly.map σ) = 0 := by
  have hm := (CPolynomial.monic_toPoly_iff _).mp hh
  have hn : σ (CPolynomial.NormProducts.norm h.natDegree h g) =
      Polynomial.resultant (h.toPoly.map σ) (g.toPoly.map σ) := by
    rw [CPolynomial.natDegree_toPoly,
      CPolynomial.NormProducts.map_norm_eq_algebraNorm _ _ _ hh,
      Polynomial.norm_adjoinRoot_eq_resultant _ _ (hm.map σ)]
  have hc := congrArg σ (Matrix.det_eq_sign_charpoly_coeff
    (CPolynomial.NormProducts.multiplicationMatrix h.natDegree h g))
  rw [← characteristicPolynomial_toPoly, ← CPolynomial.coeff_toPoly] at hc
  change σ (CPolynomial.NormProducts.norm h.natDegree h g) = _ at hc
  rw [hn, map_mul, map_pow, map_neg, map_one] at hc
  rw [hc, mul_eq_zero, or_iff_right]
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

/-- Generic coprimality over any extension of the coefficient ring makes the first coefficient
of the nonuniversal factor nonzero. -/
theorem characteristicPolynomial_coeff_zero_ne_of_isCoprime {K : Type*} [Field K]
    (σ : CPolynomial E →+* K) (q g : CPolynomial (CPolynomial E)) (hq : q.monic)
    (hcop : IsCoprime (q.toPoly.map σ) (g.toPoly.map σ)) :
    (characteristicPolynomial q g).coeff 0 ≠ 0 := by
  intro hz
  have hres := (characteristicPolynomial_coeff_zero_map_iff σ q g hq).mp (by rw [hz, map_zero])
  exact Polynomial.resultant_ne_zero _ _ hcop hres

/-- A common specialized root makes the constant coefficient vanish, even in a ramified fiber. -/
theorem characteristicPolynomial_coeff_zero_of_point {K : Type*} [Field K]
    (σ : CPolynomial E →+* K) (v : K) (q g : CPolynomial (CPolynomial E)) (hq : q.monic)
    (hqv : (q.toPoly.map σ).eval v = 0) (hgv : (g.toPoly.map σ).eval v = 0) :
    σ ((characteristicPolynomial q g).coeff 0) = 0 := by
  apply (characteristicPolynomial_coeff_zero_map_iff σ q g hq).mpr
  apply Polynomial.resultant_eq_zero_iff.mpr
  refine ⟨Or.inl (((CPolynomial.monic_toPoly_iff _).mp hq).map σ).ne_zero, ?_⟩
  intro hc
  obtain ⟨a, b, hab⟩ := hc
  have he := congrArg (Polynomial.eval v) hab
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, hqv, hgv,
    mul_zero, zero_add] at he
  exact zero_ne_one he

/-- The direct coefficient scan conceptually discards exactly the universal factor's `W`-power. -/
theorem residualFilter?_factorization {L : Type*} [Field L]
    (σ : CPolynomial E →+* L) (d q g : CPolynomial (CPolynomial E))
    (hd : d.monic) (hq : q.monic) (hdg : d.toPoly ∣ g.toPoly)
    (hcop : IsCoprime (q.toPoly.map σ) (g.toPoly.map σ)) :
    residualFilter? (d * q) g =
      some ((characteristicPolynomial q g).coeff 0).monicNormalize := by
  have hn := characteristicPolynomial_coeff_zero_ne_of_isCoprime σ q g hq hcop
  have hfac : characteristicPolynomial (d * q) g =
      CPolynomial.X ^ d.natDegree * characteristicPolynomial q g := by
    rw [characteristicPolynomial_mul d q g hd hq, characteristicPolynomial_of_dvd d g hd hdg]
  have hcoeff : (characteristicPolynomial (d * q) g).coeff d.natDegree =
      (characteristicPolynomial q g).coeff 0 := by
    rw [hfac, CPolynomial.coeff_toPoly, CPolynomial.toPoly_mul, CPolynomial.toPoly_pow,
      CPolynomial.X_toPoly, Polynomial.coeff_X_pow_mul']
    simp only [le_refl, ↓reduceIte, Nat.sub_self, ← CPolynomial.coeff_toPoly]
  have hscan : lowestCoefficient? (characteristicPolynomial (d * q) g) =
      some ((characteristicPolynomial q g).coeff 0) := by
    apply (lowestCoefficient?_eq_some_iff _ _).mpr
    refine ⟨hn, d.natDegree, ?_, hcoeff, ?_⟩
    · by_contra hlt
      have hz := Polynomial.coeff_eq_zero_of_natDegree_lt
        (p := (characteristicPolynomial (d * q) g).toPoly)
        (n := d.natDegree)
        (by simpa only [← CPolynomial.natDegree_toPoly] using Nat.lt_of_not_ge hlt)
      rw [← CPolynomial.coeff_toPoly, hcoeff] at hz
      exact hn hz
    · intro i hi
      rw [hfac, CPolynomial.coeff_toPoly, CPolynomial.toPoly_mul, CPolynomial.toPoly_pow,
        CPolynomial.X_toPoly, Polynomial.coeff_X_pow_mul', if_neg (Nat.not_le.mpr hi)]
  simp only [residualFilter?, normalizedLowestCoefficient?, hscan, Option.map_some]

/-- Every agreeing point on a generically nonuniversal factor is detected by the direct filter.
The point may also lie on a universal factor; intersections require no exclusion. -/
theorem residualFilter?_vanishes_of_nonuniversal_point
    {L K : Type*} [Field L] [Field K] (σ : CPolynomial E →+* L)
    (phi : E →+* K) (u v : K) (d q g : CPolynomial (CPolynomial E))
    (hd : d.monic) (hq : q.monic) (hdg : d.toPoly ∣ g.toPoly)
    (hcop : IsCoprime (q.toPoly.map σ) (g.toPoly.map σ))
    (hqv : (q.toPoly.map ((Polynomial.eval₂RingHom phi u).comp
      CPolynomial.toPolyRingHom)).eval v = 0)
    (hgv : (g.toPoly.map ((Polynomial.eval₂RingHom phi u).comp
      CPolynomial.toPolyRingHom)).eval v = 0)
    (c : CPolynomial E) (hc : residualFilter? (d * q) g = some c) :
    c.toPoly.eval₂ phi u = 0 := by
  have heq := residualFilter?_factorization σ d q g hd hq hdg hcop
  rw [hc] at heq
  have heqc := Option.some.inj heq
  rw [heqc, monicNormalize_eval₂_eq_zero_iff]
  simpa only [RingHom.comp_apply, CPolynomial.toPolyRingHom_apply,
    Polynomial.coe_eval₂RingHom] using characteristicPolynomial_coeff_zero_of_point
      ((Polynomial.eval₂RingHom phi u).comp CPolynomial.toPolyRingHom) v q g hq hqv hgv

open Polynomial.FunctionFieldAlgorithms

/-- The coefficient homomorphism into the generic function field. -/
noncomputable def genericCoefficientMap : CPolynomial E →+* RatFunc E :=
  (algebraMap (Polynomial E) (RatFunc E)).comp CPolynomial.toPolyRingHom

theorem valueGlobal_eq_map (h : CBivariate E) :
    ClearDenominators.valueGlobal h = (CPolynomial.toPoly h).map genericCoefficientMap := by
  rw [ClearDenominators.valueGlobal, CBivariate.toPoly_eq_map, Polynomial.map_map]
  rfl

/-- A point on the descended generic nonuniversal complement is detected by the direct
coefficient filter. Only the generic chart is reduced; specialized fibers may be nonreduced. -/
theorem residualFilter?_vanishes_of_complement_point
    {K : Type*} [Field K] (phi : E →+* K) (u v : K)
    (h g : CBivariate E) (hh : h.monic)
    (hs : Squarefree (ClearDenominators.valueGlobal h))
    (hqv : ComponentDescent.evalAt phi u v (ComponentDescent.exactComplement h g) = 0)
    (hgv : ComponentDescent.evalAt phi u v g = 0)
    (c : CPolynomial E) (hc : residualFilter? h g = some c) :
    c.toPoly.eval₂ phi u = 0 := by
  classical
  let d := ComponentDescent.monicGlobalGcd h g
  let q := ComponentDescent.exactComplement h g
  have hd := ComponentDescent.monicGlobalGcd_monic h g hh
  have hq : q.monic := by
    simpa only [ComponentRemoval.retain, pow_one] using ComponentRemoval.retain_monic h g 1 hh
  have hdg : CPolynomial.toPoly d ∣ CPolynomial.toPoly g := by
    apply (Polynomial.map_dvd_map (CPolynomial.ringEquiv (R := E)).toRingHom
      (CPolynomial.ringEquiv (R := E)).injective
      ((CPolynomial.monic_toPoly_iff _).mp hd)).mp
    have hsem := ComponentDescent.monicGlobalGcd_semantic_dvd_right h g hh
    rw [CBivariate.toPoly_eq_map, CBivariate.toPoly_eq_map] at hsem
    convert hsem using 1 <;> congr 1
  have hcop : IsCoprime ((CPolynomial.toPoly q).map genericCoefficientMap)
      ((CPolynomial.toPoly g).map genericCoefficientMap) := by
    simpa only [← valueGlobal_eq_map] using
      ComponentDescent.divByMonic_generic_isCoprime h g hh hs
  have hfac : d * q = h := ComponentDescent.monicGlobalGcd_mul_divByMonic h g hh
  have heval (a : CBivariate E) : ComponentDescent.evalAt phi u v a =
      ((CPolynomial.toPoly a).map ((Polynomial.eval₂RingHom phi u).comp
        CPolynomial.toPolyRingHom)).eval v := by
    rw [ComponentDescent.evalAt, CBivariate.toPoly_eq_map, Polynomial.eval₂_map,
      Polynomial.eval_map]
    congr 1
  apply residualFilter?_vanishes_of_nonuniversal_point genericCoefficientMap
    phi u v d q g hd hq hdg hcop _ _ c (by rwa [hfac])
  · rwa [← heval]
  · rwa [← heval]

/-- A global monic subcomponent generically coprime to the residual lies in its descended
nonuniversal complement. This divisibility holds before specialization. -/
theorem component_dvd_complement (h g a : CBivariate E) (hh : h.monic) (ha : a.monic)
    (had : CBivariate.toPoly a ∣ CBivariate.toPoly h)
    (hag : IsCoprime (ClearDenominators.valueGlobal a) (ClearDenominators.valueGlobal g)) :
    CBivariate.toPoly a ∣ CBivariate.toPoly (ComponentDescent.exactComplement h g) := by
  classical
  have ham : (CBivariate.toPoly a).Monic := by
    rw [CBivariate.toPoly_eq_map]
    exact ((CPolynomial.monic_toPoly_iff _).mp ha).map _
  apply NormalizationArithmetic.primitive_dvd_of_valueGlobal_dvd ham.isPrimitive
  have had' : ClearDenominators.valueGlobal a ∣ ClearDenominators.valueGlobal h :=
    Polynomial.map_dvd _ had
  have hdg : ClearDenominators.valueGlobal (ComponentDescent.monicGlobalGcd h g) ∣
      ClearDenominators.valueGlobal g :=
    Polynomial.map_dvd _ (ComponentDescent.monicGlobalGcd_semantic_dvd_right h g hh)
  have hfac := congrArg (ClearDenominators.valueGlobal (F := E))
    (ComponentDescent.monicGlobalGcd_mul_divByMonic h g hh)
  rw [ClearDenominators.valueGlobal_mul] at hfac
  rw [← hfac] at had'
  exact (hag.of_isCoprime_of_dvd_right hdg).dvd_of_dvd_mul_left had'

/-- Agreement on any generically nonuniversal monic subcomponent forces the direct filter
to vanish. The subcomponent need not be irreducible and its special fiber may be nonreduced. -/
theorem residualFilter?_vanishes_of_component_point
    {K : Type*} [Field K] (phi : E →+* K) (u v : K)
    (h g a : CBivariate E) (hh : h.monic) (ha : a.monic)
    (hs : Squarefree (ClearDenominators.valueGlobal h))
    (had : CBivariate.toPoly a ∣ CBivariate.toPoly h)
    (hag : IsCoprime (ClearDenominators.valueGlobal a) (ClearDenominators.valueGlobal g))
    (hav : ComponentDescent.evalAt phi u v a = 0)
    (hgv : ComponentDescent.evalAt phi u v g = 0)
    (c : CPolynomial E) (hc : residualFilter? h g = some c) :
    c.toPoly.eval₂ phi u = 0 := by
  apply residualFilter?_vanishes_of_complement_point phi u v h g hh hs _ hgv c hc
  obtain ⟨r, hr⟩ := component_dvd_complement h g a hh ha had hag
  rw [ComponentDescent.evalAt, hr, Polynomial.eval₂_mul]
  change ComponentDescent.evalAt phi u v a * _ = 0
  rw [hav, zero_mul]

/-- The proof-only component scan supplies a filter root at every nonuniversal agreeing row. -/
theorem residualFilter?_vanishes_of_scan_point
    {K : Type*} [Field K] (phi : E →+* K) (u v : K)
    (h : CBivariate E) (gs : List (CBivariate E)) (hh : h.monic)
    (hs : Squarefree (ClearDenominators.valueGlobal h))
    (a : ComponentDescent.Block E) (ha : a ∈ (ComponentDescent.run h gs).blocks)
    (i : ℕ) (g : CBivariate E) (hi : gs[i]? = some g) (hni : i ∉ a.universal)
    (hav : ComponentDescent.evalAt phi u v a.modulus = 0)
    (hgv : ComponentDescent.evalAt phi u v g = 0)
    (c : CPolynomial E) (hc : residualFilter? h g = some c) :
    c.toPoly.eval₂ phi u = 0 := by
  classical
  apply residualFilter?_vanishes_of_component_point phi u v h g a.modulus hh
    (ComponentDescent.run_monic h gs hh a ha) hs _
    ((ComponentDescent.run_genericClassified h gs hh hs i g hi a ha).2 hni) hav hgv c hc
  have hd : a.modulus ∣ h := by
    rw [← ComponentDescent.run_product h gs hh]
    exact List.dvd_prod (List.mem_map.mpr ⟨a, ha, rfl⟩)
  exact map_dvd CBivariate.ringEquiv hd

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates
