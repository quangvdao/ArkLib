/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.UniversalAgreementBound
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Contract

/-! # Initial-coordinate identities of actual constructed charts -/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ConstructorNonconstant

open CompPoly CPoly
open ReedSolomon.HiddenDerivative ReedSolomon.HiddenDerivative.FastTaylor

variable {E : Type*} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E]

/-- The actual stored initial numerators recover the projected initial coordinates in every
coefficient algebra killing the chart equation. No reducedness or point extraction is used. -/
theorem construct_initial_numerator {r k : ℕ} (p Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial (r + 2) E) (component : CMvPolynomial (r + 1) E)
    (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (chart : ChartData E r k) (hc : construct? p r k Bjet center T component values = some chart)
    {A : Type*} [CommRing A] (base : E →+* A) (point : Fin (r + 1) → A)
    (hz : CMvPolynomial.eval₂ base point chart.equation = 0)
    (j : Fin (r + 1)) (hjk : j.val < k) :
    CMvPolynomial.eval₂ base point (chart.numerators ⟨j.val, hjk⟩) =
      CMvPolynomial.eval₂ base point chart.denominator *
        CMvPolynomial.eval₂ base point (Geometry.linearCoordinate chart.projection j) := by
  obtain ⟨hden, hnum⟩ := construct?_cleared_global p Bjet center T component values hv hB
    chart hc base point hz
  rw [hnum, hden]
  let ψ := (CMvPolynomial.eval₂Hom base point).comp (projectionHom chart.projection)
  have hscalar : ∀ x, ψ (CMvPolynomial.C x) = base x := by
    intro x
    change CMvPolynomial.eval₂ base point
      (Geometry.projectPolynomial chart.projection (CMvPolynomial.C x)) = _
    rw [Geometry.projectPolynomial, CMvPolynomial.bind₁_C]
    simp [eval₂_equiv, CMvPolynomial.fromCMvPolynomial_C]
  change ψ (toCMvPolynomial (commonTaylorNumerator center (semanticEquation T) k
    ⟨j.val, hjk⟩)) = ψ (toCMvPolynomial (_ ^ (2 * k))) * _
  rw [hom_eq_eval ψ base hscalar, hom_eq_eval ψ base hscalar,
    fromCMvPolynomial_toCMvPolynomial, fromCMvPolynomial_toCMvPolynomial]
  have he : 2 * (j.val - r) - 1 = 0 := by omega
  rw [commonTaylorNumerator, rationalTaylorNumerator, dif_pos j.isLt]
  simp only [he,
    Nat.sub_zero, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_pow]
  change ψ (CMvPolynomial.X j) * _ = _ * _
  rw [mul_comm]
  congr 1
  change CMvPolynomial.eval₂ base point
    (Geometry.projectPolynomial chart.projection (CMvPolynomial.X j)) = _
  rw [Geometry.projectPolynomial, CMvPolynomial.bind₁_X]

omit [DecidableEq E] in
/-- Linear coordinates commute with arbitrary coefficient embeddings. -/
theorem eval₂_linearCoordinate {n : ℕ} {A : Type*} [CommRing A]
    (base : E →+* A) (point : Fin n → A) (M : Matrix (Fin n) (Fin n) E) (i : Fin n) :
    CMvPolynomial.eval₂ base point (Geometry.linearCoordinate M i) =
      (M.map base).mulVec point i := by
  rw [eval₂_equiv, Geometry.from_linearCoordinate]
  simp [Matrix.mulVec, dotProduct]

/-- Invert the actual chart projection using the first `r + 1` rational numerators.
This identity discharges the coordinate-recovery input to component nonconstancy. -/
theorem construct_coordinate_eq_sum_ratios {r k : ℕ} (p Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial (r + 2) E) (component : CMvPolynomial (r + 1) E)
    (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (chart : ChartData E r k) (hc : construct? p r k Bjet center T component values = some chart)
    {A : Type*} [Field A] (base : E →+* A) (point : Fin (r + 1) → A)
    (hz : CMvPolynomial.eval₂ base point chart.equation = 0)
    (hden : CMvPolynomial.eval₂ base point chart.denominator ≠ 0) :
    ∃ hbound : r < k, ∀ i,
      point i = ∑ j : Fin (r + 1), base (chart.inverseProjection i j) *
        (CMvPolynomial.eval₂ base point (chart.numerators ⟨j.val, by omega⟩) /
          CMvPolynomial.eval₂ base point chart.denominator) := by
  have hg := construct?_geometry p r k Bjet center T component values chart hc
  have hrk := hg.1.2.1
  refine ⟨hrk, ?_⟩
  intro i
  have hratio (j : Fin (r + 1)) :
      CMvPolynomial.eval₂ base point (chart.numerators ⟨j.val, by omega⟩) /
          CMvPolynomial.eval₂ base point chart.denominator =
        (chart.projection.map base).mulVec point j := by
    rw [construct_initial_numerator p Bjet center T component values hv hB chart hc
      base point hz j (by omega), eval₂_linearCoordinate]
    exact mul_div_cancel_left₀ _ hden
  simp_rw [hratio]
  change point i = ((chart.inverseProjection.map base).mulVec
    ((chart.projection.map base).mulVec point)) i
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hg.2.2.2.1]
  simp

/-- A constructed chart has a nonconstant stored ratio whenever one of its coordinates is
not a base-field scalar. The constructor's inverse projection supplies the entire argument. -/
theorem construct_exists_ratio_not_base {r k : ℕ} (p Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial (r + 2) E) (component : CMvPolynomial (r + 1) E)
    (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (chart : ChartData E r k) (hc : construct? p r k Bjet center T component values = some chart)
    {A : Type*} [Field A] (base : E →+* A) (point : Fin (r + 1) → A)
    (hz : CMvPolynomial.eval₂ base point chart.equation = 0)
    (hden : CMvPolynomial.eval₂ base point chart.denominator ≠ 0)
    (hparameter : ∃ i, ∀ c : E, point i ≠ base c) :
    ∃ j : Fin k, ∀ c : E,
      CMvPolynomial.eval₂ base point (chart.numerators j) /
        CMvPolynomial.eval₂ base point chart.denominator ≠ base c := by
  classical
  by_contra h
  push Not at h
  choose coeff hcoeff using h
  obtain ⟨hrk, hcoord⟩ := construct_coordinate_eq_sum_ratios p Bjet center T component values
    hv hB chart hc base point hz hden
  obtain ⟨i, hi⟩ := hparameter
  apply hi (∑ j : Fin (r + 1), chart.inverseProjection i j * coeff ⟨j.val, by omega⟩)
  rw [hcoord i, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hcoeff, _root_.map_mul]

omit [DecidableEq E] [BEq E] [LawfulBEq E] in
/-- An injective parameter-polynomial embedding certifies that its variable is not a
base scalar. Monic positive-degree component quotients retain this embedding. -/
theorem parameter_not_base {A : Type*} [CommRing A] (base : E →+* A)
    (parameter : Polynomial E →+* A) (hinj : Function.Injective parameter)
    (hbase : ∀ c, parameter (Polynomial.C c) = base c) :
    ∀ c, parameter Polynomial.X ≠ base c := by
  intro c hc
  have he : (Polynomial.X : Polynomial E) = Polynomial.C c := hinj (hc.trans (hbase c).symm)
  exact Polynomial.X_ne_C c he

open Polynomial Polynomial.JetHornerMachine

omit [DecidableEq E] [BEq E] [LawfulBEq E] in
/-- Descent of a polynomial forces descent of every entry in its physical descending list,
including leading zeros. -/
theorem entries_base_of_polynomial_map {A : Type*} [Field A] (base : E →+* A)
    (cs : List A) (p : E[X]) (hp : coefficientPolynomial cs = p.map base) :
    ∀ c ∈ cs, ∃ b, c = base b := by
  induction cs generalizing p with
  | nil => simp
  | cons c cs ih =>
    have hc : c = base (p.coeff cs.length) := by
      have he := congrArg (fun q : A[X] => q.coeff cs.length) hp
      simpa only [coeff_coefficientPolynomial_cons_length, coeff_map] using he
    have ht : coefficientPolynomial cs =
        (p - C (p.coeff cs.length) * X ^ cs.length).map base := by
      rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, ← hp, coefficientPolynomial_cons, ← hc]
      ring
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨_, hc⟩
    · exact ih _ ht d hd

/-- The stored descending rational message of an actual chart cannot descend to the base
field when one coordinate is transcendental over it. Any faithful monic component's generic
parameter supplies that coordinate. -/
theorem construct_message_not_base {r k : ℕ} (p Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial (r + 2) E) (component : CMvPolynomial (r + 1) E)
    (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (chart : ChartData E r k) (hc : construct? p r k Bjet center T component values = some chart)
    {A : Type*} [Field A] (base : E →+* A) (point : Fin (r + 1) → A)
    (hz : CMvPolynomial.eval₂ base point chart.equation = 0)
    (hden : CMvPolynomial.eval₂ base point chart.denominator ≠ 0)
    (hparameter : ∃ i, ∀ c : E, point i ≠ base c) :
    ∀ q : E[X], coefficientPolynomial (List.ofFn fun j : Fin k =>
      CMvPolynomial.eval₂ base point (chart.numerators j) /
        CMvPolynomial.eval₂ base point chart.denominator) ≠ q.map base := by
  intro q hq
  obtain ⟨j, hj⟩ := construct_exists_ratio_not_base p Bjet center T component values hv hB
    chart hc base point hz hden hparameter
  obtain ⟨b, hb⟩ := entries_base_of_polynomial_map base _ q hq _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  exact hj b hb

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ConstructorNonconstant
