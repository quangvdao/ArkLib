/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Contract
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Components.FirstOrder
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.ChartPolynomials
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.SeparablePartCorrectness
public import CompPoly.Bivariate.CMvEquiv

/-!
# Squarefreeness across a computed Taylor chart

An invertible linear chart projection is a ring automorphism of the stored multivariate
polynomial ring.  This file transports squarefreeness through that automorphism and through the
constructor's nonzero scalar normalization, then uses chart monicity to pass to the generic
fiber polynomial over the rational function field.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer

open CompPoly CPoly CPolynomial CPoly.TaylorReconstruction
open ReedSolomon.HiddenDerivative FastTaylor
open Polynomial.FunctionFieldAlgorithms

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Ring equivalences preserve squarefreeness in both directions. -/
private theorem squarefree_equiv {R S : Type*} [CommMonoid R] [CommMonoid S]
    (e : R ≃* S) (x : R) : Squarefree (e x) ↔ Squarefree x := by
  constructor
  · intro hx d hd
    rcases hd with ⟨c, hc⟩
    have hmap : e d * e d ∣ e x := by
      refine ⟨e c, ?_⟩
      simpa only [_root_.map_mul] using congrArg e hc
    exact (isUnit_map_iff e d).mp (hx (e d) hmap)
  · intro hx d hd
    obtain ⟨c, rfl⟩ := e.surjective d
    rw [isUnit_map_iff]
    apply hx c
    rcases hd with ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := e.surjective z
    refine ⟨w, e.injective ?_⟩
    simpa only [_root_.map_mul] using hz

/-- Applying inverse linear coordinates after forward linear coordinates is the identity. -/
private theorem projectPolynomial_roundtrip {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) E) (hMN : M * N = 1)
    (q : CMvPolynomial n E) :
    Geometry.projectPolynomial N (Geometry.projectPolynomial M q) = q := by
  apply CPoly.fromCMvPolynomial_injective
  rw [Geometry.from_projectPolynomial, Geometry.from_projectPolynomial]
  rw [MvPolynomial.comp_aeval_apply]
  have hcoordinates :
      (fun i => MvPolynomial.aeval
        (fun i => ∑ j, MvPolynomial.C (N i j) * MvPolynomial.X j)
        (∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j)) =
      (fun i => MvPolynomial.X i) := by
    funext i
    simp only [_root_.map_sum, _root_.map_mul, MvPolynomial.aeval_def,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
    calc
      (∑ x, MvPolynomial.C (M i x) * ∑ j, MvPolynomial.C (N x j) * MvPolynomial.X j) =
          ∑ x, ∑ j, MvPolynomial.C (M i x * N x j) * MvPolynomial.X j := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [← mul_assoc, ← MvPolynomial.C_mul]
      _ = ∑ j, ∑ x, MvPolynomial.C (M i x * N x j) * MvPolynomial.X j :=
        Finset.sum_comm
      _ = ∑ j, MvPolynomial.C (∑ x, M i x * N x j) * MvPolynomial.X j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_mul, _root_.map_sum]
      _ = MvPolynomial.X i := by
        have hij (j : Fin n) : (∑ x, M i x * N x j) = (1 : Matrix (Fin n) (Fin n) E) i j := by
          simpa only [Matrix.mul_apply] using congrFun (congrFun hMN i) j
        simp_rw [hij]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          have hij' : i ≠ j := Ne.symm hji
          simp [hij']
        · simp
  rw [hcoordinates, MvPolynomial.aeval_def]
  simpa only [MvPolynomial.algebraMap_eq] using MvPolynomial.eval₂_eta (fromCMvPolynomial q)

/-- An explicitly supplied two-sided matrix inverse makes linear projection a ring equivalence. -/
private noncomputable def projectEquiv {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) E) (hMN : M * N = 1) (hNM : N * M = 1) :
    CMvPolynomial n E ≃+* CMvPolynomial n E where
  toFun := Geometry.projectPolynomial M
  invFun := Geometry.projectPolynomial N
  left_inv := projectPolynomial_roundtrip M N hMN
  right_inv := projectPolynomial_roundtrip N M hNM
  map_add' := CMvPolynomial.bind₁_add _
  map_mul' := CMvPolynomial.bind₁_mul _

private theorem storedMv_hom_ext {A : Type*} [CommRing A] {n : ℕ}
    (f g : CMvPolynomial n E →+* A)
    (hC : ∀ a, f (CMvPolynomial.C a) = g (CMvPolynomial.C a))
    (hX : ∀ i, f (CMvPolynomial.X i) = g (CMvPolynomial.X i)) : f = g := by
  have hc (a : E) : CPoly.polyRingEquiv.symm (MvPolynomial.C a) =
      (CMvPolynomial.C a : CMvPolynomial n E) := by
    apply CPoly.polyRingEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    exact (CMvPolynomial.fromCMvPolynomial_C a).symm
  have hx (i : Fin n) : CPoly.polyRingEquiv.symm (MvPolynomial.X i) =
      (CMvPolynomial.X i : CMvPolynomial n E) := by
    apply CPoly.polyRingEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    exact (CMvPolynomial.fromCMvPolynomial_X i).symm
  have he : f.comp CPoly.polyRingEquiv.symm.toRingHom =
      g.comp CPoly.polyRingEquiv.symm.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa [hc] using hC a
    · intro i
      simpa [hx] using hX i
  ext q
  simpa using RingHom.congr_fun he (CPoly.polyRingEquiv q)

/-- The mathematical nested-polynomial view with ordinary variable order `[U,V]`. -/
private noncomputable def ordinaryNestedEquiv :
    CMvPolynomial 2 E ≃+* Polynomial (Polynomial E) :=
  CPoly.polyRingEquiv |>.trans
    ((MvPolynomial.renameEquiv E (Equiv.swap 0 1)).toRingEquiv |>.trans
      ((MvPolynomial.finSuccEquiv E 1).toRingEquiv |>.trans
        (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv E (Fin 1)).toRingEquiv)))

private noncomputable def nestedScalarHom : E →+* Polynomial (Polynomial E) :=
  Polynomial.C.comp Polynomial.C

private noncomputable def nestedVariables : Fin 2 → Polynomial (Polynomial E) :=
  ![Polynomial.C Polynomial.X, Polynomial.X]

private theorem ordinaryNestedEquiv_semantics (q : CMvPolynomial 2 E) :
    ordinaryNestedEquiv q =
      MvPolynomial.eval₂ nestedScalarHom nestedVariables (fromCMvPolynomial q) := by
  rw [ordinaryNestedEquiv]
  let e : MvPolynomial (Fin 2) E ≃+* Polynomial (Polynomial E) :=
    (MvPolynomial.renameEquiv E (Equiv.swap 0 1)).toRingEquiv |>.trans
      ((MvPolynomial.finSuccEquiv E 1).toRingEquiv |>.trans
        (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv E (Fin 1)).toRingEquiv))
  change e (fromCMvPolynomial q) = _
  generalize fromCMvPolynomial q = Q
  induction Q using MvPolynomial.induction_on with
  | C a =>
      simp [e, nestedScalarHom, MvPolynomial.finSuccEquiv_apply,
        MvPolynomial.uniqueAlgEquiv_apply]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      rw [e.map_mul, hP, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      congr 1
      fin_cases i
      · dsimp [e, nestedVariables]
        rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
          Equiv.swap_apply_left]
        rw [Polynomial.mapEquiv_apply]
        have hs : (MvPolynomial.finSuccEquiv E 1) (MvPolynomial.X 1) =
            Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
          convert MvPolynomial.finSuccEquiv_X_succ (R := E) (j := (0 : Fin 1))
          apply Fin.ext
          rfl
        rw [hs, Polynomial.map_C]
        congr 1
        simp [MvPolynomial.uniqueAlgEquiv_apply]
      · dsimp [e, nestedVariables]
        rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
          Equiv.swap_apply_right]
        rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.mapEquiv_apply, Polynomial.map_X]

private theorem toPoly_fromOrdinaryCMv (q : CMvPolynomial 2 E) :
    CBivariate.toPoly (BivariateReducedSupport.fromOrdinaryCMv q) =
      MvPolynomial.eval₂ nestedScalarHom nestedVariables (fromCMvPolynomial q) := by
  classical
  let h := CBivariate.toPolyRingHom (R := E)
  have heq := MvPolynomial.eval₂_comp_left h
    (CPolynomial.CHom.comp CPolynomial.CHom)
    ![CPolynomial.C CPolynomial.X, CPolynomial.X]
    (fromCMvPolynomial q)
  rw [BivariateReducedSupport.fromOrdinaryCMv, CPoly.eval₂_equiv]
  change h _ = _
  rw [heq]
  congr 1
  · ext a
    simp [h, nestedScalarHom, CBivariate.toPolyRingHom, CBivariate.ringEquiv,
      CBivariate.toPoly_eq_map, CPolynomial.C_toPoly]
  · funext i
    fin_cases i <;>
      simp [h, nestedVariables, CBivariate.toPolyRingHom, CBivariate.ringEquiv,
        CBivariate.toPoly_eq_map, CPolynomial.C_toPoly, CPolynomial.X_toPoly]

private theorem toPoly_bivariatePolynomial (q : CMvPolynomial 2 E) :
    CBivariate.toPoly (ChartPolynomials.bivariatePolynomial q) =
      MvPolynomial.eval₂ nestedScalarHom nestedVariables (fromCMvPolynomial q) := by
  change CBivariate.toPoly (BivariateReducedSupport.fromOrdinaryCMv q) = _
  exact toPoly_fromOrdinaryCMv q

private theorem ordinaryNestedEquiv_eq (q : CMvPolynomial 2 E) :
    ordinaryNestedEquiv q =
      CBivariate.toPoly (ChartPolynomials.bivariatePolynomial q) := by
  rw [ordinaryNestedEquiv_semantics, toPoly_bivariatePolynomial]

/-- Squarefreeness of the supplied ordinary component survives the constructor's invertible
linear projection and nonzero monic normalization, and hence holds over the chart's generic
function field. -/
theorem construct?_genericSquarefree
    [DecidableEq E] (p Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial 3 E) (component : CMvPolynomial 2 E) (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    {k : ℕ} (chart : ChartData E 1 k)
    (hc : FastTaylor.construct? p 1 k Bjet center T component values = some chart)
    (hcomponentSquarefree : Squarefree
      (CBivariate.toPoly (BivariateReducedSupport.fromOrdinaryCMv component))) :
    Squarefree (ClearDenominators.valueGlobal
      (ChartPolynomials.bivariatePolynomial chart.equation)) := by
  have hgeometry := FastTaylor.construct?_geometry
    p 1 k Bjet center T component values chart hc
  have hnormal := FastTaylor.construct?_normalForms
    p 1 k Bjet center T component values hv hB chart hc
  have hcomponentNested : Squarefree (ordinaryNestedEquiv component) := by
    rw [ordinaryNestedEquiv_semantics, ← toPoly_fromOrdinaryCMv]
    exact hcomponentSquarefree
  have hcomponentStored : Squarefree component :=
    (squarefree_equiv ordinaryNestedEquiv.toMulEquiv component).mp hcomponentNested
  have hprojected : Squarefree
      (Geometry.projectPolynomial chart.projection component) :=
    (squarefree_equiv
      (projectEquiv chart.projection chart.inverseProjection
        hgeometry.2.2.1 hgeometry.2.2.2.1).toMulEquiv component).mpr hcomponentStored
  let scalar : E :=
    ((Geometry.Direction.homogeneousPart component.totalDegree component).eval
      (fun i => chart.projection i (Fin.last 1)))⁻¹
  have hscalar : scalar ≠ 0 := by
    intro hs
    have hequationZero : chart.equation = 0 := by
      rw [hgeometry.2.2.2.2.1]
      simp only [Geometry.MonicProjection.normalize, scalar] at hs ⊢
      rw [hs]
      have hCzero : (CMvPolynomial.C 0 : CMvPolynomial 2 E) = 0 := by
        apply CPoly.fromCMvPolynomial_injective
        rw [CMvPolynomial.fromCMvPolynomial_C, CPoly.map_zero, MvPolynomial.C_0]
      rw [hCzero, MulZeroClass.zero_mul]
    have hmonic := hnormal.1
    rw [hequationZero] at hmonic
    have hsplit : splitLast (0 : CMvPolynomial 2 E) = 0 :=
      map_zero (splitLast (E := E) (r := 1))
    rw [hsplit] at hmonic
    have hpolyMonic := (CPolynomial.monic_toPoly_iff
      (0 : CPolynomial (CMvPolynomial 1 E))).mp hmonic
    rw [CPolynomial.toPoly_zero] at hpolyMonic
    exact Polynomial.not_monic_zero hpolyMonic
  have hconstantUnit : IsUnit (CMvPolynomial.C scalar : CMvPolynomial 2 E) := by
    change IsUnit ((algebraMap E (CMvPolynomial 2 E)) scalar)
    exact (isUnit_iff_ne_zero.mpr hscalar).map (algebraMap E (CMvPolynomial 2 E))
  have hequationAssociated : Associated chart.equation
      (Geometry.projectPolynomial chart.projection component) := by
    rw [hgeometry.2.2.2.2.1]
    change Associated (CMvPolynomial.C scalar *
      Geometry.projectPolynomial chart.projection component)
      (Geometry.projectPolynomial chart.projection component)
    exact associated_unit_mul_left _ _ hconstantUnit
  have hequationStored : Squarefree chart.equation :=
    hequationAssociated.squarefree_iff.mpr hprojected
  have hequationNested : Squarefree
      (CBivariate.toPoly (ChartPolynomials.bivariatePolynomial chart.equation)) := by
    rw [← ordinaryNestedEquiv_eq]
    exact (squarefree_equiv ordinaryNestedEquiv.toMulEquiv chart.equation).mpr
      hequationStored
  have houterMonic :
      (ChartPolynomials.bivariatePolynomial chart.equation).toPoly.Monic :=
    (CPolynomial.monic_toPoly_iff _).mp
      (ChartPolynomials.equation_monic_of_normalForms chart hnormal)
  have hprimitive :
      (CBivariate.toPoly (ChartPolynomials.bivariatePolynomial chart.equation)).IsPrimitive := by
    rw [CBivariate.toPoly_eq_map]
    exact (houterMonic.map CPolynomial.ringEquiv.toRingHom).isPrimitive
  exact SeparablePartCorrectness.squarefree_valueGlobal hprimitive hequationNested

/-- The actual first-order regular-part producer supplies the squarefree premise needed by the
constructor theorem, so no separate generic-squarefreeness assumption remains. -/
theorem construct?_firstOrder_genericSquarefree
    [DecidableEq E] (p Bjet : ℕ) [Fact p.Prime] [CharP E p] (inverse : E → E) (center : E)
    (T : CMvPolynomial 3 E) (data : RegularPart.Data E)
    (hinverse : p ≤ (ClearDenominators.primitivePart
        (FastTaylor.ComponentConstruction.FirstOrder.specializedEquation center T)).natDegree →
      ∀ a, inverse a ^ p = a)
    (hrun : FastTaylor.ComponentConstruction.FirstOrder.run p inverse center T =
      .regularPart data)
    (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    {k : ℕ} (chart : ChartData E 1 k)
    (hc : FastTaylor.construct? p 1 k Bjet center T
      (FastTaylor.ComponentConstruction.FirstOrder.component data) values = some chart) :
    Squarefree (ClearDenominators.valueGlobal
      (ChartPolynomials.bivariatePolynomial chart.equation)) := by
  apply construct?_genericSquarefree p Bjet center T
    (FastTaylor.ComponentConstruction.FirstOrder.component data) values hv hB chart hc
  rw [FastTaylor.ComponentConstruction.FirstOrder.fromOrdinaryCMv_component]
  exact (FastTaylor.ComponentConstruction.FirstOrder.run_regularPart_certificate
    p inverse center T data hinverse hrun).split_certificate.regular_squarefree

end ReedSolomon.ListDecoding.FirstOrderNormProducer
