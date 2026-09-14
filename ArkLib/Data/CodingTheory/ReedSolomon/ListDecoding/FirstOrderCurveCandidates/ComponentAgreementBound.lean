/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ConstructorNonconstant
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ComponentRemoval
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.ComponentNorms
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Universal agreement bounds on actual descended components -/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ComponentAgreementBound

open CompPoly CPoly Polynomial Polynomial.FunctionFieldAlgorithms
open ReedSolomon.HiddenDerivative ReedSolomon.HiddenDerivative.FastTaylor
open ConstructorNonconstant

variable {E : Type} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E]

omit [DecidableEq E] in
/-- A monic component containing any geometric point has positive fiber degree. -/
theorem positive_degree_of_point {A : Type*} [Field A] (base : E →+* A) (u v : A)
    (h : CBivariate E) (hm : h.monic) (hz : ComponentDescent.evalAt base u v h = 0) :
    0 < h.natDegree := by
  by_contra hp
  have hd : h.natDegree = 0 := Nat.eq_zero_of_not_pos hp
  have ho : h = 1 := by
    apply CPolynomial.toPoly_injective
    rw [CPolynomial.toPoly_one]
    apply Polynomial.eq_one_of_monic_natDegree_zero ((CPolynomial.monic_toPoly_iff _).mp hm)
    rwa [← CPolynomial.natDegree_toPoly]
  simp [ho, ComponentDescent.evalAt, CBivariate.toPoly_eq_map, CPolynomial.toPoly_one] at hz

omit [DecidableEq E] in
/-- Evaluating the generic fiber equals bivariate evaluation at its transcendental parameter. -/
theorem eval_valueGlobal {A : Type*} [Field A] (ι : RatFunc E →+* A) (v : A)
    (h : CBivariate E) :
    (ClearDenominators.valueGlobal h).eval₂ ι v =
      ComponentDescent.evalAt (ι.comp RatFunc.C) (ι RatFunc.X) v h := by
  unfold ClearDenominators.valueGlobal ComponentDescent.evalAt
  rw [Polynomial.eval₂_map]
  congr 1
  ext c
  · simp
  · simp [RatFunc.algebraMap_X]

omit [DecidableEq E] in
/-- Positive fiber degree supplies a generic point at which a coprime obstruction is nonzero.
The algebraic closure is used only in the proof; no roots are computed by the producer. -/
theorem exists_generic_point (h s : CBivariate E) (hpos : 0 < h.natDegree)
    (hcop : IsCoprime (ClearDenominators.valueGlobal h) (ClearDenominators.valueGlobal s)) :
    ∃ v : AlgebraicClosure (RatFunc E),
      ComponentDescent.evalAt ((algebraMap (RatFunc E) (AlgebraicClosure (RatFunc E))).comp
        RatFunc.C) (algebraMap (RatFunc E) (AlgebraicClosure (RatFunc E)) RatFunc.X) v h = 0 ∧
      ComponentDescent.evalAt ((algebraMap (RatFunc E) (AlgebraicClosure (RatFunc E))).comp
        RatFunc.C) (algebraMap (RatFunc E) (AlgebraicClosure (RatFunc E)) RatFunc.X) v s ≠ 0 := by
  let ι := algebraMap (RatFunc E) (AlgebraicClosure (RatFunc E))
  have hd : (ClearDenominators.valueGlobal h).degree ≠ 0 := by
    apply ne_of_gt
    rw [← natDegree_pos_iff_degree_pos]
    unfold ClearDenominators.valueGlobal
    rw [natDegree_map_eq_of_injective (RatFunc.algebraMap_injective E),
      CBivariate.toPoly_eq_map,
      natDegree_map_eq_of_injective (CPolynomial.ringEquiv (R := E)).injective,
      ← CPolynomial.natDegree_toPoly]
    exact hpos
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_eval₂_eq_zero_of_injective ι ι.injective _ hd
  refine ⟨v, (eval_valueGlobal ι v h).symm ▸ hv, ?_⟩
  rw [← eval_valueGlobal]
  have he := Polynomial.aeval_ne_zero_of_isCoprime
    (S := AlgebraicClosure (RatFunc E)) hcop v
  exact he.resolve_left (fun hh => hh hv)

/-- Constructor denominator regularity holds over every field extension, including the
algebraic closure of the parameter function field. -/
theorem construct_denominator_ne_zero {k : ℕ} (p Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial 3 E) (component : CMvPolynomial 2 E) (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (chart : ChartData E 1 k) (hc : construct? p 1 k Bjet center T component values = some chart)
    {A : Type*} [Field A] (base : E →+* A) (point : Fin 2 → A)
    (hz : CMvPolynomial.eval₂ base point chart.equation = 0)
    (hs : CMvPolynomial.eval₂ base point chart.separant ≠ 0) :
    CMvPolynomial.eval₂ base point chart.denominator ≠ 0 := by
  have hcleared := construct?_cleared_global p Bjet center T component values hv hB
    chart hc base point hz
  have hgeometry := construct?_geometry p 1 k Bjet center T component values chart hc
  have hpower : toCMvPolynomial (initialJetSeparant center (semanticEquation T) ^ (2 * k)) =
      initialSeparant center T ^ (2 * k) := by
    apply eq_iff_fromCMvPolynomial.mpr
    rw [fromCMvPolynomial_toCMvPolynomial]
    change _ = CPoly.polyRingEquiv (initialSeparant center T ^ (2 * k))
    rw [map_pow]
    exact congrArg (fun S => S ^ (2 * k)) (initialSeparant_semantics center T).symm
  have hprojected : Geometry.projectPolynomial chart.projection
      (toCMvPolynomial (initialJetSeparant center (semanticEquation T) ^ (2 * k))) =
      chart.separant ^ (2 * k) := by
    change projectionHom chart.projection
      (toCMvPolynomial (initialJetSeparant center (semanticEquation T) ^ (2 * k))) = _
    rw [hpower, map_pow]
    change Geometry.projectPolynomial chart.projection (initialSeparant center T) ^ (2 * k) = _
    rw [hgeometry.2.2.2.2.2.2.2]
  rw [hcleared.1, hprojected]
  change CMvPolynomial.eval₂Hom base point (chart.separant ^ (2 * k)) ≠ 0
  rw [map_pow]
  exact pow_ne_zero _ hs

/-- Every positive-degree block in the executed component scan satisfies the universal
agreement bound. Generic coprimality and global divisibility are the only component inputs. -/
theorem block_universal_length_le_pred {k n : ℕ} (p Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial 3 E) (component : CMvPolynomial 2 E) (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (chart : ChartData E 1 k) (hc : construct? p 1 k Bjet center T component values = some chart)
    (h : CBivariate E) (hh : h.monic)
    (hdiv : h ∣ (chartPolynomials chart).equation)
    (hcop : IsCoprime (ClearDenominators.valueGlobal h)
      (ClearDenominators.valueGlobal (chartPolynomials chart).separant))
    (domain : Fin n ↪ E) (received : Fin n → E)
    (block : ComponentDescent.Block E)
    (hblock : block ∈ (ComponentDescent.run h
      (List.ofFn fun i : Fin n => agreementPolynomial chart (domain i) (received i))).blocks)
    (hpos : 0 < block.modulus.natDegree) : block.universal.length ≤ k - 1 := by
  classical
  let gs := List.ofFn fun i : Fin n => agreementPolynomial chart (domain i) (received i)
  have hbd : block.modulus ∣ h := by
    rw [← ComponentDescent.run_product h gs hh]
    exact List.dvd_prod (List.mem_map.mpr ⟨block, hblock, rfl⟩)
  have hgeneric : ClearDenominators.valueGlobal block.modulus ∣
      ClearDenominators.valueGlobal h := by
    obtain ⟨q, hq⟩ := hbd
    exact ⟨ClearDenominators.valueGlobal q, by rw [hq, ClearDenominators.valueGlobal_mul]⟩
  let ι := algebraMap (RatFunc E) (AlgebraicClosure (RatFunc E))
  let base := ι.comp RatFunc.C
  let u := ι RatFunc.X
  obtain ⟨v, hroot, hs⟩ := exists_generic_point block.modulus (chartPolynomials chart).separant
    hpos (hcop.of_isCoprime_of_dvd_left hgeneric)
  have eval_dvd (a b : CBivariate E) (hab : CBivariate.toPoly a ∣ CBivariate.toPoly b)
      (ha : ComponentDescent.evalAt base u v a = 0) :
      ComponentDescent.evalAt base u v b = 0 := by
    obtain ⟨q, hq⟩ := hab
    unfold ComponentDescent.evalAt at *
    rw [hq, Polynomial.eval₂_mul, ha, zero_mul]
  have heq : CMvPolynomial.eval₂ base ![u, v] chart.equation = 0 := by
    have hz := eval_dvd _ _ (map_dvd CBivariate.ringEquiv (hbd.trans hdiv)) hroot
    simpa only [chartPolynomials, FirstOrderNormProducer.ChartPolynomials.ofChart,
      FirstOrderNormProducer.componentEvalAt_eq_evalNested,
      FirstOrderNormProducer.evalNested_bivariatePolynomial] using hz
  have hsep : CMvPolynomial.eval₂ base ![u, v] chart.separant ≠ 0 := by
    simpa only [chartPolynomials, FirstOrderNormProducer.ChartPolynomials.ofChart,
      FirstOrderNormProducer.componentEvalAt_eq_evalNested,
      FirstOrderNormProducer.evalNested_bivariatePolynomial] using hs
  have hden := construct_denominator_ne_zero p Bjet center T component values hv hB chart hc
    base ![u, v] heq hsep
  have hparam : ∃ i : Fin 2, ∀ c : E,
      (![u, v] : Fin 2 → AlgebraicClosure (RatFunc E)) i ≠ base c := by
    refine ⟨0, ?_⟩
    apply parameter_not_base base (ι.comp (algebraMap E[X] (RatFunc E)))
      (ι.injective.comp (RatFunc.algebraMap_injective E))
    intro c
    simp [base]
  have hlabels : ∀ i ∈ block.universal, i < n := by
    intro i hi
    simpa [gs] using ComponentDescent.run_labels_lt h gs block hblock i hi
  let d : ℕ → E := fun i => if hi : i < n then domain ⟨i, hi⟩ else 0
  let w : ℕ → E := fun i => if hi : i < n then received ⟨i, hi⟩ else 0
  have hbnd := construct_universal_card_le_pred p Bjet center T component values hv hB chart hc
    base ![u, v] heq hden hparam block.universal.toFinset d w (by
      intro i hi j hj hij
      have hi' := hlabels i (List.mem_toFinset.mp hi)
      have hj' := hlabels j (List.mem_toFinset.mp hj)
      simp only [d, dif_pos hi', dif_pos hj'] at hij
      exact congrArg Fin.val (domain.injective hij)) (by
      intro i hi
      have hi' := hlabels i (List.mem_toFinset.mp hi)
      have hdvd := ComponentDescent.run_universal_dvd h gs hh i
        (agreementPolynomial chart (domain ⟨i, hi'⟩) (received ⟨i, hi'⟩))
        (by simp [gs, hi']) block hblock (List.mem_toFinset.mp hi)
      have hz := eval_dvd _ _ hdvd hroot
      simpa only [agreementPolynomial, FirstOrderNormProducer.ChartPolynomials.agreement,
        FirstOrderNormProducer.componentEvalAt_eq_evalNested,
        FirstOrderNormProducer.evalNested_bivariatePolynomial, d, w, dif_pos hi'] using hz)
  rwa [List.toFinset_card_of_nodup (ComponentDescent.run_labels_nodup h gs block hblock)] at hbnd

/-- Removing the closed separant components discharges all generic hypotheses of the
per-block universal-agreement bound for an actual first-order chart. -/
theorem retained_block_universal_length_le_pred {k n : ℕ} (p Bjet : ℕ) [CharP E p]
    (center : E) (T : CMvPolynomial 3 E) (component : CMvPolynomial 2 E) (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (chart : ChartData E 1 k) (hc : construct? p 1 k Bjet center T component values = some chart)
    (domain : Fin n ↪ E) (received : Fin n → E) (block : ComponentDescent.Block E)
    (hblock : block ∈ (ComponentDescent.run
      (ComponentRemoval.retain (chartPolynomials chart).equation (chartPolynomials chart).separant
        (chartPolynomials chart).equation.natDegree)
      (List.ofFn fun i : Fin n => agreementPolynomial chart (domain i) (received i))).blocks)
    (hpos : 0 < block.modulus.natDegree) : block.universal.length ≤ k - 1 := by
  have hh := equation_monic_of_normalForms chart
    (construct?_normalForms p 1 k Bjet center T component values hv hB chart hc)
  apply block_universal_length_le_pred p Bjet center T component values hv hB chart hc _
    (ComponentRemoval.retain_monic _ _ _ hh) _
    (ComponentRemoval.retain_degree_generic_isCoprime _ _ hh) domain received block hblock hpos
  refine ⟨ComponentRemoval.removed (chartPolynomials chart).equation
    (chartPolynomials chart).separant (chartPolynomials chart).equation.natDegree, ?_⟩
  rw [mul_comm, ComponentRemoval.product _ _ _ hh]

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ComponentAgreementBound
