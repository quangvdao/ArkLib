/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.Coverage

/-!
# Universal agreements on a nonconstant message family

Two distinct polynomials of degree below `k` cannot agree at `k` distinct evaluation
positions. Consequently a component whose rational message varies has at most `k - 1`
universally agreeing positions. The parameter space is arbitrary: repeated fibers and
intersections do not affect this argument. Nonconstancy must concern the message, rather
than merely the curve or its parameter; a constant message on a nonconstant curve is
insufficient.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.UniversalAgreementBound

open Polynomial

variable {L I T : Type*} [Field L] {k : ℕ}

/-- Polynomial uniqueness forces every member of a universally agreeing family to coincide
once the number of distinct positions reaches its degree bound. -/
theorem eq_of_universal_agreements (message : T → L[X])
    (hdegree : ∀ t, (message t).degree < k) (positions : Finset I)
    (domain received : I → L) (hinj : Set.InjOn domain positions)
    (hagree : ∀ t i, i ∈ positions → (message t).eval (domain i) = received i)
    (hcard : k ≤ positions.card) (s t : T) : message s = message t := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq positions hinj
  · exact (hdegree s).trans_le (by exact_mod_cast hcard)
  · exact (hdegree t).trans_le (by exact_mod_cast hcard)
  · intro i hi
    exact (hagree s i hi).trans (hagree t i hi).symm

/-- A nonconstant message family has strictly fewer than `k` universal agreements. -/
theorem card_lt_of_nonconstant (message : T → L[X])
    (hdegree : ∀ t, (message t).degree < k)
    (hnonconstant : ∃ s t, message s ≠ message t) (positions : Finset I)
    (domain received : I → L) (hinj : Set.InjOn domain positions)
    (hagree : ∀ t i, i ∈ positions → (message t).eval (domain i) = received i) :
    positions.card < k := by
  by_contra h
  obtain ⟨s, t, hst⟩ := hnonconstant
  exact hst (eq_of_universal_agreements message hdegree positions domain received hinj
    hagree (Nat.le_of_not_gt h) s t)

/-- The conventional `k - 1` form also covers the natural-number boundary. -/
theorem card_le_pred_of_nonconstant (message : T → L[X])
    (hdegree : ∀ t, (message t).degree < k)
    (hnonconstant : ∃ s t, message s ≠ message t) (positions : Finset I)
    (domain received : I → L) (hinj : Set.InjOn domain positions)
    (hagree : ∀ t i, i ∈ positions → (message t).eval (domain i) = received i) :
    positions.card ≤ k - 1 := by
  have := card_lt_of_nonconstant message hdegree hnonconstant positions domain received hinj hagree
  omega

/-- Over a component's function field, `k` universal agreements force the generic message
to descend to the coefficient field. This formulation needs no geometric-point witnesses. -/
theorem eq_map_interpolate_of_agreements {F : Type*} [Field F] [DecidableEq I]
    (ι : F →+* L) (message : L[X]) (hdegree : message.degree < k)
    (positions : Finset I) (domain received : I → F)
    (hinj : Set.InjOn domain positions)
    (hagree : ∀ i ∈ positions, message.eval (ι (domain i)) = ι (received i))
    (hcard : k ≤ positions.card) :
    message = (Lagrange.interpolate positions domain received).map ι := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq positions
    (v := fun i => ι (domain i))
  · intro i hi j hj hij
    exact hinj hi hj (ι.injective hij)
  · exact hdegree.trans_le (by exact_mod_cast hcard)
  · exact degree_map_le.trans_lt (Lagrange.degree_interpolate_lt received hinj)
  · intro i hi
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Lagrange.eval_interpolate_at_node received hinj hi]
    exact hagree i hi

/-- A generic component message that does not descend to the coefficient field has at most
`k - 1` universal agreements. For a function field, non-descent is the algebraic form of
nonconstancy; unlike a point count, it remains useful over finite coefficient fields. -/
theorem card_le_pred_of_not_base_defined {F : Type*} [Field F]
    (ι : F →+* L) (message : L[X]) (hdegree : message.degree < k)
    (hnonconstant : ∀ p : F[X], message ≠ p.map ι)
    (positions : Finset I) (domain received : I → F)
    (hinj : Set.InjOn domain positions)
    (hagree : ∀ i ∈ positions, message.eval (ι (domain i)) = ι (received i)) :
    positions.card ≤ k - 1 := by
  classical
  have hlt : positions.card < k := by
    by_contra h
    exact hnonconstant _ (eq_map_interpolate_of_agreements ι message hdegree
      positions domain received hinj hagree (Nat.le_of_not_gt h))
  omega

open ReedSolomon.HiddenDerivative.FastTaylor Polynomial.JetHornerMachine

variable {E : Type} [Field E] [BEq E] [LawfulBEq E]
  {L : Type} [Field L]

/-- The stored rational numerator vector has width `k`, even at a ramified point. -/
theorem degree_rationalPolynomial_lt (chart : ChartData E 1 k) (ι : E →+* L) (u v : L) :
    (Coverage.rationalPolynomial chart ι u v).degree < k := by
  simpa only [Coverage.rationalPolynomial, List.length_map, List.length_ofFn] using
    degree_coefficientPolynomial_lt_length
      ((List.ofFn (chartPolynomials chart).numerators).map fun numerator =>
        TowerRepresentation.evalNested numerator ι u v /
          TowerRepresentation.evalNested (chartPolynomials chart).denominator ι u v)

/-- Apply the bound to any chosen locus of a chart, including one irreducible component.
The locus may contain intersection points and may be a fiber with multiplicity. The two
witnesses certify that the rational *message* varies on this particular locus. -/
theorem chart_card_le_pred (chart : ChartData E 1 k) (ι : E →+* L)
    (locus : Set (L × L))
    (hnonconstant : ∃ s t : locus,
      Coverage.rationalPolynomial chart ι s.val.1 s.val.2 ≠
        Coverage.rationalPolynomial chart ι t.val.1 t.val.2)
    (positions : Finset I) (domain received : I → L)
    (hinj : Set.InjOn domain positions)
    (hagree : ∀ p ∈ locus, ∀ i ∈ positions,
      (Coverage.rationalPolynomial chart ι p.1 p.2).eval (domain i) = received i) :
    positions.card ≤ k - 1 :=
  card_le_pred_of_nonconstant
    (fun p : locus => Coverage.rationalPolynomial chart ι p.val.1 p.val.2)
    (fun p => degree_rationalPolynomial_lt chart ι p.val.1 p.val.2)
    hnonconstant positions domain received hinj
    (fun p i hi => hagree p.val p.property i hi)

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.UniversalAgreementBound
