module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Components.Recursive
public import ArkLib.Data.Polynomial.ResultantTotalDegree
public import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Certified readiness of a retained general component

This module connects the executable general-component producer to the executable monic projection
and confluent sample searches.  Its main results require exactly a `General.Certificate`, a nonzero
input equation, identification of the supplied separant with the final-variable partial derivative,
and an input total-degree budget.  A fixed-chart result additionally requires the actual successful
`MonicProjection.construct?` equality.  The end-to-end existence result replaces that equality by a
positive-degree premise for the retained component and a distinct-value prefix of length greater
than `max Bjet (2 * Bjet * (Bjet - 1))`.

No coverage schedule, factor list, assumed normalization witness, or assumed obstruction enters
these results.
-/

@[expose] public section

open CompPoly CPoly CPoly.TaylorReconstruction
open ReedSolomon.HiddenDerivative.FastTaylor

namespace ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction.Readiness

variable {E : Type*} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E] {r : ℕ}

omit [DecidableEq E] in
theorem projectPolynomial_comp
    (M N : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (p : CMvPolynomial (r + 1) E) :
    Geometry.projectPolynomial N (Geometry.projectPolynomial M p) =
      Geometry.projectPolynomial (M * N) p := by
  apply CPoly.fromCMvPolynomial_injective
  simp only [Geometry.from_projectPolynomial, MvPolynomial.comp_aeval_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  · intro i
    simp only [MvPolynomial.aeval_eq_bind₁, map_sum, _root_.map_mul,
      MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, MvPolynomial.bind₁_X_right,
      Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring

omit [DecidableEq E] in
theorem projectPolynomial_one (p : CMvPolynomial (r + 1) E) :
    Geometry.projectPolynomial 1 p = p := by
  apply CPoly.fromCMvPolynomial_injective
  rw [Geometry.from_projectPolynomial]
  have h : MvPolynomial.aeval (fun i : Fin (r + 1) =>
      ∑ j, MvPolynomial.C ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i j) *
        MvPolynomial.X j) =
      AlgHom.id E (MvPolynomial (Fin (r + 1)) E) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, AlgHom.id_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Matrix.one_apply, if_neg (Ne.symm hji)]
      simp
    · simp
  exact DFunLike.congr_fun h (fromCMvPolynomial p)

def projectionEquiv
    (M N : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hMN : M * N = 1) (hNM : N * M = 1) :
    CMvPolynomial (r + 1) E ≃+* CMvPolynomial (r + 1) E where
  toFun := Geometry.projectPolynomial M
  invFun := Geometry.projectPolynomial N
  left_inv p := by rw [projectPolynomial_comp, hMN, projectPolynomial_one]
  right_inv p := by rw [projectPolynomial_comp, hNM, projectPolynomial_one]
  map_add' p q := by simp [Geometry.projectPolynomial]
  map_mul' p q := by simp [Geometry.projectPolynomial]

omit [DecidableEq E] in
@[simp] theorem projectionEquiv_apply
    (M N : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hMN : M * N = 1) (hNM : N * M = 1) (p : CMvPolynomial (r + 1) E) :
    projectionEquiv M N hMN hNM p = Geometry.projectPolynomial M p := rfl

def splitLastEquiv :
    CMvPolynomial (r + 1) E ≃+* CPolynomial (CMvPolynomial r E) where
  toFun := splitLast
  invFun := flattenLast
  left_inv := flattenLast_splitLast
  right_inv := splitLast_flattenLast
  map_add' := map_add splitLast
  map_mul' := map_mul splitLast

@[simp] theorem splitLastEquiv_apply (p : CMvPolynomial (r + 1) E) :
    splitLastEquiv p = splitLast p := rfl

@[simp] theorem splitLastEquiv_symm_apply (p : CPolynomial (CMvPolynomial r E)) :
    splitLastEquiv.symm p = flattenLast p := rfl

theorem isRelPrime_map_equiv {R S : Type*} [Semiring R] [Semiring S]
    (e : R ≃+* S) {a b : R} (h : IsRelPrime a b) : IsRelPrime (e a) (e b) := by
  apply IsRelPrime.of_map e.symm
  simpa only [e.symm_apply_apply] using h

theorem isRelPrime_of_primitive_generic_coprime
    (p q : CPolynomial (CMvPolynomial r E)) (hp : p.toPoly.IsPrimitive)
    (hcoprime : IsCoprime
      (p.toPoly.map (algebraMap (CMvPolynomial r E)
        (FractionRing (CMvPolynomial r E))))
      (q.toPoly.map (algebraMap (CMvPolynomial r E)
        (FractionRing (CMvPolynomial r E))))) :
    IsRelPrime p q := by
  let R := CMvPolynomial r E
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hpoly : IsRelPrime p.toPoly q.toPoly := by
    intro d hdp hdq
    have hdPrimitive := Polynomial.isPrimitive_of_dvd hp hdp
    apply (hdPrimitive.isUnit_iff_isUnit_map (K := K)).mpr
    have hdpm : Polynomial.map f d ∣ Polynomial.map f p.toPoly :=
      map_dvd (Polynomial.mapRingHom f) hdp
    have hdqm : Polynomial.map f d ∣ Polynomial.map f q.toPoly :=
      map_dvd (Polynomial.mapRingHom f) hdq
    exact hcoprime.isRelPrime hdpm hdqm
  simpa only [← CPolynomial.ringEquiv_apply, RingEquiv.symm_apply_apply] using
    (isRelPrime_map_equiv CPolynomial.ringEquiv.symm hpoly)
set_option maxHeartbeats 1000000 in
-- Lifting a field divisor through integral closure is substantially costlier than the caller.
theorem generic_coprime_of_monic_isRelPrime
    (p q : CPolynomial (CMvPolynomial r E)) (hp : p.monic)
    (hrel : IsRelPrime p q) :
    IsCoprime
      (p.toPoly.map (algebraMap (CMvPolynomial r E)
        (FractionRing (CMvPolynomial r E))))
      (q.toPoly.map (algebraMap (CMvPolynomial r E)
        (FractionRing (CMvPolynomial r E)))) := by
  let R := CMvPolynomial r E
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  let _ : IsIntegrallyClosed (MvPolynomial (Fin r) E) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  let _ : IsIntegrallyClosed R :=
    IsIntegrallyClosed.of_equiv (CPoly.polyRingEquiv (n := r) (R := E)).symm
  have hpPoly : p.toPoly.Monic := (CPolynomial.monic_toPoly_iff p).mp hp
  have hrelPoly : IsRelPrime p.toPoly q.toPoly := by
    simpa only [CPolynomial.ringEquiv_apply] using
      (isRelPrime_map_equiv CPolynomial.ringEquiv hrel)
  apply IsRelPrime.isCoprime
  intro d hdp hdq
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (hpPoly.map f).ne_zero hdp
  obtain ⟨d', hd'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hpPoly hdp
  have hlc : d.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hd0
  have hd'map : d'.map f = d * Polynomial.C d.leadingCoeff⁻¹ := by
    apply mul_right_cancel₀ (Polynomial.C_ne_zero.mpr hlc)
    rw [mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hlc, Polynomial.C_1, mul_one, hd']
  have hd'Monic : d'.Monic :=
    (IsFractionRing.injective R K).monic_map_iff.mpr <| hd'map.symm ▸
      Polynomial.monic_mul_leadingCoeff_inv hd0
  have hunitC : IsUnit (Polynomial.C d.leadingCoeff⁻¹) :=
    Polynomial.isUnit_C.mpr (inv_ne_zero hlc).isUnit
  have hd'pMap : d'.map f ∣ p.toPoly.map f := by
    rw [hd'map]
    exact (associated_mul_unit_left d _ hunitC).dvd_iff_dvd_left.mpr hdp
  have hd'qMap : d'.map f ∣ q.toPoly.map f := by
    rw [hd'map]
    exact (associated_mul_unit_left d _ hunitC).dvd_iff_dvd_left.mpr hdq
  have hd'p : d' ∣ p.toPoly := hpPoly.dvd_of_fraction_map_dvd_fraction_map hd'Monic hd'pMap
  have hd'q : d' ∣ q.toPoly := hd'Monic.isPrimitive.dvd_of_fraction_map_dvd_fraction_map hd'qMap
  have hd'Unit : IsUnit d' := hrelPoly hd'p hd'q
  have hd'MapUnit : IsUnit (d'.map f) := hd'Unit.map (Polynomial.mapRingHom f)
  rw [hd'map] at hd'MapUnit
  exact isUnit_of_mul_isUnit_left hd'MapUnit

open ComponentConstruction.General Geometry.MonicProjection

theorem projected_generic_coprime
    {equation separant : CMvPolynomial (r + 1) E}
    {data : ComponentConstruction.General.Data r E}
    (certificate : ComponentConstruction.General.Certificate equation separant data)
    (hequation : equation ≠ 0)
    (hseparant : separant = CMvPolynomial.partialDerivative (Fin.last r) equation)
    (values : List E) (g : Geometry.MonicProjection.Data r E)
    (hg : Geometry.MonicProjection.construct?
      (ComponentConstruction.General.component data) values = some g) :
    IsCoprime
      ((splitLast g.polynomial).toPoly.map
        (algebraMap (CMvPolynomial r E) (FractionRing (CMvPolynomial r E))))
      ((splitLast (Geometry.projectPolynomial g.forward separant)).toPoly.map
        (algebraMap (CMvPolynomial r E) (FractionRing (CMvPolynomial r E)))) := by
  obtain ⟨hMN, hNM, _, hpolynomial, hmonic, _, _⟩ :=
    Geometry.MonicProjection.construct?_sound
      (ComponentConstruction.General.component data) values g hg
  have hsourceNested : IsRelPrime data.regular (splitLast separant) :=
    isRelPrime_of_primitive_generic_coprime data.regular (splitLast separant)
      certificate.regular_primitive
      (certificate.regular_isCoprime_separant hequation hseparant)
  have hsourceFlat : IsRelPrime
      (ComponentConstruction.General.component data) separant := by
    simpa [ComponentConstruction.General.component] using
      (isRelPrime_map_equiv (splitLastEquiv (E := E) (r := r)).symm hsourceNested)
  have hprojected : IsRelPrime
      (Geometry.projectPolynomial g.forward
        (ComponentConstruction.General.component data))
      (Geometry.projectPolynomial g.forward separant) := by
    simpa using isRelPrime_map_equiv
      (projectionEquiv g.forward g.inverse hMN hNM) hsourceFlat
  let scalar := ((Geometry.Direction.homogeneousPart
      (ComponentConstruction.General.component data).totalDegree
      (ComponentConstruction.General.component data)).eval
        (fun i => g.forward i (Fin.last r)))⁻¹
  have hchart : g.polynomial = CMvPolynomial.C scalar *
      Geometry.projectPolynomial g.forward
        (ComponentConstruction.General.component data) := by
    rw [hpolynomial, Geometry.MonicProjection.normalize]
  have hchartNe : g.polynomial ≠ 0 := by
    intro hz
    have hm := (CPolynomial.monic_toPoly_iff (splitLast g.polynomial)).mp hmonic
    rw [hz, _root_.map_zero splitLast, CPolynomial.toPoly_zero] at hm
    exact hm.ne_zero rfl
  have hscalar : scalar ≠ 0 := by
    intro hs
    apply hchartNe
    rw [hchart, hs]
    apply CPoly.fromCMvPolynomial_injective
    rw [CPoly.map_mul, CMvPolynomial.fromCMvPolynomial_C,
      MvPolynomial.C_0, zero_mul, CPoly.map_zero]
  have hscalarUnit : IsUnit (CMvPolynomial.C scalar : CMvPolynomial (r + 1) E) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨CMvPolynomial.C scalar⁻¹, ?_⟩
    apply CPoly.fromCMvPolynomial_injective
    rw [CPoly.map_mul, CMvPolynomial.fromCMvPolynomial_C,
      CMvPolynomial.fromCMvPolynomial_C, ← MvPolynomial.C_mul,
      mul_inv_cancel₀ hscalar, MvPolynomial.C_1, CPoly.map_one]
  have hchartRel : IsRelPrime g.polynomial
      (Geometry.projectPolynomial g.forward separant) := by
    rw [hchart, isRelPrime_mul_unit_left_left hscalarUnit]
    exact hprojected
  have hnested : IsRelPrime (splitLast g.polynomial)
      (splitLast (Geometry.projectPolynomial g.forward separant)) := by
    simpa using isRelPrime_map_equiv (splitLastEquiv (E := E) (r := r)) hchartRel
  exact generic_coprime_of_monic_isRelPrime _ _ hmonic hnested

theorem projected_obstruction_ne_zero
    {equation separant : CMvPolynomial (r + 1) E}
    {data : ComponentConstruction.General.Data r E}
    (certificate : ComponentConstruction.General.Certificate equation separant data)
    (hequation : equation ≠ 0)
    (hseparant : separant = CMvPolynomial.partialDerivative (Fin.last r) equation)
    (values : List E) (g : Geometry.MonicProjection.Data r E)
    (hg : Geometry.MonicProjection.construct?
      (ComponentConstruction.General.component data) values = some g) :
    ConfluentSample.obstruction g.polynomial
      (Geometry.projectPolynomial g.forward separant) ≠ 0 := by
  apply ConfluentSample.obstruction_ne_zero_of_generic_coprime
    (algebraMap (CMvPolynomial r E) (FractionRing (CMvPolynomial r E)))
    (IsFractionRing.injective _ _)
  exact projected_generic_coprime certificate hequation hseparant values g hg



theorem totalDegree_pderiv_le_sub
    {σ R : Type*} [CommSemiring R] (i : σ) (p : MvPolynomial σ R) :
    (MvPolynomial.pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  have hpderiv : MvPolynomial.pderiv i p =
      ∑ s ∈ p.support, MvPolynomial.pderiv i
        (MvPolynomial.monomial s (p.coeff s)) := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum]
  rw [hpderiv]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  rw [MvPolynomial.pderiv_monomial]
  by_cases hcoeff : p.coeff s * (s i : R) = 0
  · simp [hcoeff]
  have hi : 0 < s i := by
    by_contra hi
    have : s i = 0 := Nat.eq_zero_of_not_pos hi
    simp [this] at hcoeff
  have hdecomp : s - Finsupp.single i 1 + Finsupp.single i 1 = s := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
      omega
    · simp [hji]
  have hdegree : (s - Finsupp.single i 1).degree ≤ s.degree - 1 := by
    have := congrArg Finsupp.degree hdecomp
    simp only [_root_.map_add, Finsupp.degree_single] at this
    omega
  calc
    (MvPolynomial.monomial (s - Finsupp.single i 1)
      (p.coeff s * (s i : R))).totalDegree ≤
        (s - Finsupp.single i 1).degree :=
      MvPolynomial.totalDegree_monomial_le _ _
    _ ≤ s.degree - 1 := hdegree
    _ ≤ p.totalDegree - 1 := Nat.sub_le_sub_right (Finset.le_sup hs) 1


structure OuterCoefficientDegreeBudgets
    (P Q : CPolynomial (CMvPolynomial r E)) (Bjet : ℕ) : Prop where
  componentOuter : P.natDegree ≤ Bjet
  separantOuter : Q.natDegree ≤ Bjet - 1
  componentCoefficient : ∀ j,
    (fromCMvPolynomial (P.coeff j)).totalDegree ≤ Bjet
  separantCoefficient : ∀ j,
    (fromCMvPolynomial (Q.coeff j)).totalDegree ≤ Bjet - 1

omit [DecidableEq E] in
theorem natDegree_le_of_weightedDegreeLE
    (p : CPolynomial (CMvPolynomial r E)) {L : ℕ}
    (hp : WeightedDegreeLE p L) : p.natDegree ≤ L := by
  classical
  by_cases hz : p = 0
  · rw [hz, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero,
      Polynomial.natDegree_zero]
    exact Nat.zero_le L
  have hc : p.coeff p.natDegree ≠ 0 := by
    rw [CPolynomial.coeff_toPoly, CPolynomial.natDegree_toPoly,
      Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr <| by
      intro h
      apply hz
      apply CPolynomial.toPoly_injective
      rw [h, CPolynomial.toPoly_zero]
  exact (Nat.le_add_left p.natDegree _).trans (hp p.natDegree hc)

theorem projected_degree_budgets
    {equation separant : CMvPolynomial (r + 1) E}
    {data : ComponentConstruction.General.Data r E}
    (certificate : ComponentConstruction.General.Certificate equation separant data)
    (hequation : equation ≠ 0)
    (hseparant : separant = CMvPolynomial.partialDerivative (Fin.last r) equation)
    (Bjet : ℕ) (hequationDegree : (fromCMvPolynomial equation).totalDegree ≤ Bjet)
    (values : List E) (g : Geometry.MonicProjection.Data r E)
    (hg : Geometry.MonicProjection.construct?
      (ComponentConstruction.General.component data) values = some g) :
    OuterCoefficientDegreeBudgets
      (splitLast g.polynomial)
      (splitLast (Geometry.projectPolynomial g.forward separant)) Bjet := by
  obtain ⟨_, _, _, _, _, hdegree, hweighted⟩ :=
    Geometry.MonicProjection.construct?_sound
      (ComponentConstruction.General.component data) values g hg
  rw [CPoly.totalDegree_equiv (S := E)] at hdegree
  have hcomponentDegree :
      (fromCMvPolynomial (ComponentConstruction.General.component data)).totalDegree ≤ Bjet :=
    (certificate.component_totalDegree_le hequation).trans hequationDegree
  have hseparantDegree : (fromCMvPolynomial separant).totalDegree ≤ Bjet - 1 := by
    rw [hseparant, CMvPolynomial.fromCMvPolynomial_partialDerivative]
    exact (totalDegree_pderiv_le_sub (Fin.last r) (fromCMvPolynomial equation)).trans
      (Nat.sub_le_sub_right hequationDegree 1)
  have hprojectedSeparantDegree :
      (fromCMvPolynomial (Geometry.projectPolynomial g.forward separant)).totalDegree ≤
        Bjet - 1 :=
    (Geometry.totalDegree_projectPolynomial_le g.forward separant).trans hseparantDegree
  have hseparantWeighted : WeightedDegreeLE
      (splitLast (Geometry.projectPolynomial g.forward separant)) (Bjet - 1) :=
    weightedDegreeLE_splitLast _ hprojectedSeparantDegree
  refine
    { componentOuter := hdegree.le.trans hcomponentDegree
      separantOuter := natDegree_le_of_weightedDegreeLE _ hseparantWeighted
      componentCoefficient := fun j =>
        (totalDegree_coeff_le_of_weightedDegreeLE _ hweighted j).trans hcomponentDegree
      separantCoefficient := fun j =>
        totalDegree_coeff_le_of_weightedDegreeLE _ hseparantWeighted j }


theorem projected_obstruction_totalDegree_le
    {equation separant : CMvPolynomial (r + 1) E}
    {data : ComponentConstruction.General.Data r E}
    (certificate : ComponentConstruction.General.Certificate equation separant data)
    (hequation : equation ≠ 0)
    (hseparant : separant = CMvPolynomial.partialDerivative (Fin.last r) equation)
    (Bjet : ℕ) (hequationDegree : (fromCMvPolynomial equation).totalDegree ≤ Bjet)
    (values : List E) (g : Geometry.MonicProjection.Data r E)
    (hg : Geometry.MonicProjection.construct?
      (ComponentConstruction.General.component data) values = some g) :
    (fromCMvPolynomial (ConfluentSample.obstruction g.polynomial
      (Geometry.projectPolynomial g.forward separant))).totalDegree ≤
        2 * Bjet * (Bjet - 1) := by
  let P := splitLast g.polynomial
  let Q := splitLast (Geometry.projectPolynomial g.forward separant)
  let e := CPoly.polyRingEquiv (n := r) (R := E)
  have hbudgets := projected_degree_budgets certificate hequation hseparant Bjet
    hequationDegree values g hg
  have hPdegree : (P.toPoly.map e.toRingHom).natDegree ≤ Bjet := by
    rw [Polynomial.natDegree_map_eq_of_injective e.injective,
      ← CPolynomial.natDegree_toPoly]
    exact hbudgets.componentOuter
  have hQdegree : (Q.toPoly.map e.toRingHom).natDegree ≤ Bjet - 1 := by
    rw [Polynomial.natDegree_map_eq_of_injective e.injective,
      ← CPolynomial.natDegree_toPoly]
    exact hbudgets.separantOuter
  have hPcoeff : ∀ j, ((P.toPoly.map e.toRingHom).coeff j).totalDegree ≤ Bjet := by
    intro j
    rw [Polynomial.coeff_map, ← CPolynomial.coeff_toPoly]
    exact hbudgets.componentCoefficient j
  have hQcoeff : ∀ j, ((Q.toPoly.map e.toRingHom).coeff j).totalDegree ≤ Bjet - 1 := by
    intro j
    rw [Polynomial.coeff_map, ← CPolynomial.coeff_toPoly]
    exact hbudgets.separantCoefficient j
  have hresultant := Polynomial.totalDegree_resultant_le_two_mul_degreeBudget
    (P.toPoly.map e.toRingHom) (Q.toPoly.map e.toRingHom) Bjet
    hPdegree hQdegree hPcoeff hQcoeff
  change (e (ArkLib.Rojas.Producer.Univariate.storedResultant P Q
    P.natDegree Q.natDegree)).totalDegree ≤ _
  rw [ArkLib.Rojas.Producer.Univariate.storedResultant_eq]
  change (e.toRingHom (Polynomial.resultant P.toPoly Q.toPoly
    P.natDegree Q.natDegree)).totalDegree ≤ _
  rw [← Polynomial.resultant_map_map P.toPoly Q.toPoly P.natDegree Q.natDegree e.toRingHom,
    CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly,
    ← Polynomial.natDegree_map_eq_of_injective (f := e.toRingHom) e.injective P.toPoly,
    ← Polynomial.natDegree_map_eq_of_injective (f := e.toRingHom) e.injective Q.toPoly]
  exact hresultant


/-- A nonempty producer component list places the retained component in the
positive-degree branch. -/
theorem component_totalDegree_pos_of_components_ne_nil
    (data : ComponentConstruction.General.Data r E)
    (hcomponents : ComponentConstruction.General.components data ≠ []) :
    0 < (ComponentConstruction.General.component data).totalDegree := by
  have hregular : 0 < data.regular.natDegree := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hcomponents ((ComponentConstruction.General.components_eq_nil_iff data).mpr hzero)
  rw [CPoly.totalDegree_equiv (S := E)]
  apply hregular.trans_le
  have hweighted := weightedDegreeLE_splitLast
    (ComponentConstruction.General.component data) le_rfl
  simpa [ComponentConstruction.General.component] using
    natDegree_le_of_weightedDegreeLE
      (splitLast (ComponentConstruction.General.component data)) hweighted

/-- A distinct prefix longer than both the equation budget and the resultant envelope guarantees
that the actual projection search and the actual confluent-sample search both succeed.  The only
extra branch premise is that the retained component is nonconstant. -/
theorem exists_projection_and_confluent_sample
    {equation separant : CMvPolynomial (r + 1) E}
    {data : ComponentConstruction.General.Data r E}
    (certificate : ComponentConstruction.General.Certificate equation separant data)
    (hequation : equation ≠ 0)
    (hseparant : separant = CMvPolynomial.partialDerivative (Fin.last r) equation)
    (Bjet : ℕ) (hequationDegree : (fromCMvPolynomial equation).totalDegree ≤ Bjet)
    (hcomponentPositive : 0 < (ComponentConstruction.General.component data).totalDegree)
    (values : List E) (hvalues : values.Nodup)
    (hprefix : max Bjet (2 * Bjet * (Bjet - 1)) < values.length) :
    ∃ g a,
      Geometry.MonicProjection.construct?
          (ComponentConstruction.General.component data) values = some g ∧
        ConfluentSample.select? g.polynomial
          (Geometry.projectPolynomial g.forward separant) values = some a := by
  have hcomponentDegree :
      (ComponentConstruction.General.component data).totalDegree ≤ Bjet := by
    rw [CPoly.totalDegree_equiv (S := E)]
    exact (certificate.component_totalDegree_le hequation).trans hequationDegree
  obtain ⟨g, hg⟩ := Geometry.MonicProjection.construct?_exists
    (ComponentConstruction.General.component data) values
    (certificate.component_ne_zero hequation) hcomponentPositive hvalues
    (hcomponentDegree.trans_lt ((Nat.le_max_left _ _).trans_lt hprefix))
  have hobstructionNe := projected_obstruction_ne_zero certificate hequation hseparant values g hg
  have hobstructionDegree := projected_obstruction_totalDegree_le certificate hequation hseparant
    Bjet hequationDegree values g hg
  obtain ⟨a, ha⟩ := ConfluentSample.select?_exists g.polynomial
    (Geometry.projectPolynomial g.forward separant) values hobstructionNe hvalues
    (hobstructionDegree.trans_lt ((Nat.le_max_right _ _).trans_lt hprefix))
  exact ⟨g, a, hg, ha⟩


/-- The concrete recursive initial-stage producer, actual monic projection, computed obstruction,
and actual sample selector form a ready chart under the same prefix bound.  Thus callers supply no
arithmetic implementation, normalization certificate, coprimality oracle, or obstruction witness. -/
theorem recursiveInitial_projection_and_confluent_sample
    {F : Type*} [Field F] [DecidableEq F]
    (center : F) (T : CMvPolynomial (r + 2) F)
    (data : ComponentConstruction.General.Data r F)
    (hrun : ComponentConstruction.RecursiveArithmetic.runInitial? center T = some data)
    (hequation : FastTaylor.initialEquation center T ≠ 0)
    (Bjet : ℕ)
    (hequationDegree :
      (fromCMvPolynomial (FastTaylor.initialEquation center T)).totalDegree ≤ Bjet)
    (hcomponentPositive : 0 < (ComponentConstruction.General.component data).totalDegree)
    (values : List F) (hvalues : values.Nodup)
    (hprefix : max Bjet (2 * Bjet * (Bjet - 1)) < values.length) :
    ∃ g a,
      Geometry.MonicProjection.construct?
          (ComponentConstruction.General.component data) values = some g ∧
        ConfluentSample.obstruction g.polynomial
            (Geometry.projectPolynomial g.forward (FastTaylor.initialSeparant center T)) ≠ 0 ∧
        (fromCMvPolynomial (ConfluentSample.obstruction g.polynomial
          (Geometry.projectPolynomial g.forward
            (FastTaylor.initialSeparant center T)))).totalDegree ≤
              2 * Bjet * (Bjet - 1) ∧
        ConfluentSample.select? g.polynomial
          (Geometry.projectPolynomial g.forward (FastTaylor.initialSeparant center T)) values =
            some a := by
  obtain ⟨produced, hproduced, certificate⟩ :=
    ComponentConstruction.RecursiveArithmetic.runInitial?_exists_certificate center T hequation
  have hdata : produced = data := by
    rw [hrun] at hproduced
    exact (Option.some.inj hproduced).symm
  subst data
  let equation := FastTaylor.initialEquation center T
  let separant := FastTaylor.initialSeparant center T
  have hseparant : separant = CMvPolynomial.partialDerivative (Fin.last r) equation :=
    ComponentConstruction.General.initialSeparant_eq_partialDerivative_last center T
  obtain ⟨g, a, hg, ha⟩ := exists_projection_and_confluent_sample certificate hequation
    hseparant Bjet hequationDegree hcomponentPositive values hvalues hprefix
  exact ⟨g, a, hg,
    projected_obstruction_ne_zero certificate hequation hseparant values g hg,
    projected_obstruction_totalDegree_le certificate hequation hseparant Bjet
      hequationDegree values g hg,
    ha⟩

/-- The concrete readiness result stated with the producer's actual nonempty emitted-component
branch.  Positive component degree is derived rather than supplied as a separate premise. -/
theorem recursiveInitial_projection_and_confluent_sample_of_nonempty_components
    {F : Type*} [Field F] [DecidableEq F]
    (center : F) (T : CMvPolynomial (r + 2) F)
    (data : ComponentConstruction.General.Data r F)
    (hrun : ComponentConstruction.RecursiveArithmetic.runInitial? center T = some data)
    (hequation : FastTaylor.initialEquation center T ≠ 0)
    (hcomponents : ComponentConstruction.General.components data ≠ [])
    (Bjet : ℕ)
    (hequationDegree :
      (fromCMvPolynomial (FastTaylor.initialEquation center T)).totalDegree ≤ Bjet)
    (values : List F) (hvalues : values.Nodup)
    (hprefix : max Bjet (2 * Bjet * (Bjet - 1)) < values.length) :
    ∃ g a,
      Geometry.MonicProjection.construct?
          (ComponentConstruction.General.component data) values = some g ∧
        ConfluentSample.obstruction g.polynomial
            (Geometry.projectPolynomial g.forward (FastTaylor.initialSeparant center T)) ≠ 0 ∧
        (fromCMvPolynomial (ConfluentSample.obstruction g.polynomial
          (Geometry.projectPolynomial g.forward
            (FastTaylor.initialSeparant center T)))).totalDegree ≤
              2 * Bjet * (Bjet - 1) ∧
        ConfluentSample.select? g.polynomial
          (Geometry.projectPolynomial g.forward (FastTaylor.initialSeparant center T)) values =
            some a := by
  exact recursiveInitial_projection_and_confluent_sample center T data hrun hequation Bjet
    hequationDegree (component_totalDegree_pos_of_components_ne_nil data hcomponents)
    values hvalues hprefix

end ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction.Readiness
