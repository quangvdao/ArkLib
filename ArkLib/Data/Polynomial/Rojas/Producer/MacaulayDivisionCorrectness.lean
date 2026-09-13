/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.DenseMacaulayCorrectness
public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayQuotient
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-!
# Correctness of executable single-divisor reduction

This file connects the stored graded-lex leading term computation to polynomial
semantics and proves the algebraic invariant of every reduction step.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.MacaulayQuotient

open CPoly CPoly.CMvPolynomial
open DenseMacaulay
open scoped MonomialOrder

variable {F : Type*} [Field F]

private theorem list_ofFn_lex_iff : ∀ {n : ℕ} (a b : Fin n → ℕ),
    List.ofFn a < List.ofFn b ↔
      ∃ j, (∀ d, d < j → a d = b d) ∧ a j < b j := by
  intro n
  induction n with
  | zero =>
      intro a b
      simp [List.ofFn_zero]
  | succ n ih =>
      intro a b
      rw [List.ofFn_succ, List.ofFn_succ]
      change List.Lex (· < ·) (a 0 :: List.ofFn fun i => a i.succ)
          (b 0 :: List.ofFn fun i => b i.succ) ↔ _
      rw [List.cons_lex_cons_iff]
      change a 0 < b 0 ∨ a 0 = b 0 ∧
          List.ofFn (fun i => a i.succ) < List.ofFn (fun i => b i.succ) ↔ _
      rw [ih]
      constructor
      · rintro (h | ⟨hzero, j, hjprefix, hj⟩)
        · exact ⟨0, by simp, h⟩
        · refine ⟨j.succ, ?_, hj⟩
          intro d hd
          cases d using Fin.cases with
          | zero => exact hzero
          | succ d => exact hjprefix d (Fin.succ_lt_succ_iff.mp hd)
      · rintro ⟨j, hjprefix, hj⟩
        cases j using Fin.cases with
        | zero => exact Or.inl hj
        | succ i =>
            refine Or.inr ⟨hjprefix 0 (by simp [Fin.lt_def]), ?_⟩
            exact ⟨i, fun d hd => hjprefix d.succ
              (Fin.succ_lt_succ_iff.mpr hd), hj⟩

private theorem vector_toList_eq_ofFn {n : ℕ} (m : Vector ℕ n) :
    m.toList = List.ofFn m.get := by
  rw [← Vector.toList_ofFn]
  exact congrArg Vector.toList Vector.ofFn_getElem.symm

/-- Lexicographic comparison of executable exponent vectors is the same
comparison used by the mathematical finitely-supported exponent vectors. -/
theorem monomial_list_lt_iff_finsupp_lex {n : ℕ} (a b : CMvMonomial n) :
    a.toList < b.toList ↔
      Finsupp.Lex (· < ·) (· < ·) a.toFinsupp b.toFinsupp := by
  rw [vector_toList_eq_ofFn, vector_toList_eq_ofFn, list_ofFn_lex_iff,
    Finsupp.lex_def]
  rfl

/-- Executable and finitely-supported total degrees agree. -/
theorem monomial_totalDegree_eq_finsupp_degree {n : ℕ} (m : CMvMonomial n) :
    m.totalDegree = m.toFinsupp.degree := by
  rw [DenseMacaulay.totalDegree_eq_sum_get, Finsupp.degree_eq_sum]
  rfl

/-- The executable key induces exactly Mathlib's graded-lex monomial order. -/
theorem gradedLexKey_lt_iff_degLex {n : ℕ} (a b : CMvMonomial n) :
    gradedLexKey a < gradedLexKey b ↔
      a.toFinsupp ≺[MonomialOrder.degLex] b.toFinsupp := by
  rw [MonomialOrder.degLex_lt_iff, Finsupp.DegLex.lt_iff]
  simp only [gradedLexKey, Prod.Lex.toLex_lt_toLex,
    ofDegLex_toDegLex]
  rw [monomial_totalDegree_eq_finsupp_degree,
    monomial_totalDegree_eq_finsupp_degree]
  apply or_congr Iff.rfl
  apply and_congr Iff.rfl
  exact monomial_list_lt_iff_finsupp_lex a b

/-- The non-strict executable key order also agrees with graded lex. -/
theorem gradedLexKey_le_iff_degLex {n : ℕ} (a b : CMvMonomial n) :
    gradedLexKey a ≤ gradedLexKey b ↔
      a.toFinsupp ≼[MonomialOrder.degLex] b.toFinsupp := by
  rw [← not_lt, ← not_lt, gradedLexKey_lt_iff_degLex]

/-- The bounded enumeration contains exactly the monomials below its total
degree ceiling. -/
theorem mem_boundedMonomials_iff_totalDegree_le {n degree : ℕ}
    {monomial : CMvMonomial n} :
    monomial ∈ boundedMonomials n degree ↔ monomial.totalDegree ≤ degree := by
  simp only [boundedMonomials, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨weight, hweight, hmonomial⟩
    rw [mem_weakCompositions_iff_totalDegree] at hmonomial
    omega
  · intro hdegree
    exact ⟨monomial.totalDegree, by omega,
      mem_weakCompositions_of_totalDegree rfl⟩

/-- No exponent vector is repeated in the bounded enumeration. -/
theorem boundedMonomials_nodup (n degree : ℕ) :
    (boundedMonomials n degree).Nodup := by
  rw [boundedMonomials, List.nodup_flatMap]
  constructor
  · intro weight _
    exact weakCompositions_nodup n weight
  · rw [List.pairwise_iff_get]
    intro i j hij
    change List.Disjoint
      (weakCompositions n ((List.range (degree + 1)).get i))
      (weakCompositions n ((List.range (degree + 1)).get j))
    rw [List.disjoint_left]
    intro monomial hmonomialLeft hmonomialRight
    have hleftDegree := mem_weakCompositions_totalDegree hmonomialLeft
    have hrightDegree := mem_weakCompositions_totalDegree hmonomialRight
    have hijValue : (List.range (degree + 1)).get i ≠
        (List.range (degree + 1)).get j := by
      simp only [List.get_eq_getElem, List.getElem_range]
      intro hequal
      exact Fin.ne_of_lt hij (Fin.ext hequal)
    exact hijValue (hleftDegree.symm.trans hrightDegree)

/-- A returned leading term is one of the polynomial's stored nonzero terms. -/
theorem leadingTerm?_mem {n : ℕ} {p : CMvPolynomial n F}
    {term : CMvMonomial n × F} (hterm : leadingTerm? p = some term) :
    term ∈ p.val.toList := by
  exact List.argmax_mem hterm

/-- The executable leading term maximizes the graded-lex key among all stored
terms. -/
theorem gradedLexKey_le_of_leadingTerm? {n : ℕ} {p : CMvPolynomial n F}
    {leading term : CMvMonomial n × F} (hleading : leadingTerm? p = some leading)
    (hterm : term ∈ p.val.toList) :
    gradedLexKey term.1 ≤ gradedLexKey leading.1 := by
  apply List.le_of_mem_argmax
    (f := gradedLexKey ∘ Prod.fst) hterm
  simpa [leadingTerm?] using hleading

/-- A returned coefficient is the actual coefficient at its returned
monomial. -/
theorem leadingTerm?_coeff {n : ℕ} {p : CMvPolynomial n F}
    {monomial : CMvMonomial n} {coefficient : F}
    (hterm : leadingTerm? p = some (monomial, coefficient)) :
    p.coeff monomial = coefficient := by
  have hmem := leadingTerm?_mem hterm
  have hlookup :=
    Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem
  simp [CMvPolynomial.coeff, hlookup]

/-- Every coefficient stored in a lawful computable polynomial is nonzero. -/
theorem leadingTerm?_coefficient_ne_zero {n : ℕ} {p : CMvPolynomial n F}
    {monomial : CMvMonomial n} {coefficient : F}
    (hterm : leadingTerm? p = some (monomial, coefficient)) :
    coefficient ≠ 0 := by
  have hmem := leadingTerm?_mem hterm
  have hlookup :=
    Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem
  intro hzero
  subst coefficient
  exact p.property monomial hlookup

/-- The executable leading monomial is Mathlib's graded-lex degree.  This is
the bridge that permits use of the standard leading-product theorems without
putting a noncomputable monomial order in the runtime. -/
theorem leadingTerm?_degree {n : ℕ} {p : CMvPolynomial n F}
    {monomial : CMvMonomial n} {coefficient : F}
    (hterm : leadingTerm? p = some (monomial, coefficient)) :
    MonomialOrder.degLex.degree (fromCMvPolynomial p) = monomial.toFinsupp := by
  let order := MonomialOrder.degLex (σ := Fin n)
  have hcoefficient : coefficient ≠ 0 :=
    leadingTerm?_coefficient_ne_zero hterm
  have hmonomialSupport :
      monomial.toFinsupp ∈ (fromCMvPolynomial p).support := by
    rw [MvPolynomial.mem_support_iff, CPoly.coeff_eq,
      CMvMonomial.ofFinsupp_toFinsupp, leadingTerm?_coeff hterm]
    exact hcoefficient
  have hmonomialLe :
      monomial.toFinsupp ≼[order] order.degree (fromCMvPolynomial p) :=
    order.le_degree hmonomialSupport
  have hdegreeLe :
      order.degree (fromCMvPolynomial p) ≼[order] monomial.toFinsupp := by
    rw [order.degree_le_iff]
    intro exponent hexponent
    have hcoefficient' :
        p.coeff (CMvMonomial.ofFinsupp exponent) ≠ 0 := by
      simpa [CPoly.coeff_eq] using
        (MvPolynomial.mem_support_iff.mp hexponent)
    unfold CMvPolynomial.coeff at hcoefficient'
    cases hlookup :
        p.val[CMvMonomial.ofFinsupp exponent]? with
    | none => simp [hlookup] at hcoefficient'
    | some storedCoefficient =>
        have hstored :
            (CMvMonomial.ofFinsupp exponent, storedCoefficient) ∈
              p.val.toList :=
          Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hlookup
        have hkey := gradedLexKey_le_of_leadingTerm? hterm hstored
        simpa [order, gradedLexKey_le_iff_degLex] using
          (gradedLexKey_le_iff_degLex _ _).mp hkey
  apply order.toSyn.injective
  exact le_antisymm hdegreeLe hmonomialLe

/-- A returned leading monomial has the polynomial's ordinary total degree. -/
theorem leadingTerm?_totalDegree {n : ℕ} {p : CMvPolynomial n F}
    {monomial : CMvMonomial n} {coefficient : F}
    (hterm : leadingTerm? p = some (monomial, coefficient)) :
    monomial.totalDegree = p.totalDegree := by
  calc
    monomial.totalDegree = monomial.toFinsupp.degree :=
      monomial_totalDegree_eq_finsupp_degree monomial
    _ = (MonomialOrder.degLex.degree
        (fromCMvPolynomial p)).degree := by
      rw [leadingTerm?_degree hterm]
    _ = (fromCMvPolynomial p).totalDegree :=
      MvPolynomial.degree_degLexDegree
    _ = p.totalDegree := (CPoly.totalDegree_equiv (S := F)).symm

/-- Number of bounded monomials at or below a monomial in the executable
graded-lex order. -/
def monomialRank {n : ℕ} (degree : ℕ) (monomial : CMvMonomial n) : ℕ :=
  ((boundedMonomials n degree).toFinset.filter fun candidate =>
    gradedLexKey candidate ≤ gradedLexKey monomial).card

/-- Rank strictly increases along the executable graded-lex order when both
monomials lie in the bounded universe. -/
theorem monomialRank_lt {n degree : ℕ} {left right : CMvMonomial n}
    (hright : right ∈ boundedMonomials n degree)
    (hlt : gradedLexKey left < gradedLexKey right) :
    monomialRank degree left < monomialRank degree right := by
  unfold monomialRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro candidate hc
    simp only [Finset.mem_filter, List.mem_toFinset] at hc ⊢
    exact ⟨hc.1, hc.2.trans (le_of_lt hlt)⟩
  · intro hequal
    have hrightFiltered : right ∈
        (boundedMonomials n degree).toFinset.filter (fun candidate =>
          gradedLexKey candidate ≤ gradedLexKey right) := by
      simp only [Finset.mem_filter, List.mem_toFinset]
      exact ⟨hright, le_rfl⟩
    rw [← hequal] at hrightFiltered
    simp only [Finset.mem_filter, List.mem_toFinset] at hrightFiltered
    exact (not_le_of_gt hlt) hrightFiltered.2

/-- Monomial rank is bounded by the length of the enumerated universe. -/
theorem monomialRank_le_length {n degree : ℕ} (monomial : CMvMonomial n) :
    monomialRank degree monomial ≤ (boundedMonomials n degree).length := by
  unfold monomialRank
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (List.toFinset_card_le _)

/-- A monomial in the bounded universe has positive rank. -/
theorem monomialRank_pos {n degree : ℕ} {monomial : CMvMonomial n}
    (hmonomial : monomial ∈ boundedMonomials n degree) :
    0 < monomialRank degree monomial := by
  unfold monomialRank
  rw [Finset.card_pos]
  refine ⟨monomial, ?_⟩
  simp only [Finset.mem_filter, List.mem_toFinset]
  exact ⟨hmonomial, le_rfl⟩

/-- Rank of a residual, with the zero residual represented by rank zero. -/
def residualRank {n : ℕ} (degree : ℕ) (residual : CMvPolynomial n F) : ℕ :=
  match leadingTerm? residual with
  | none => 0
  | some term => monomialRank degree term.1

/-- Residual rank is bounded by the enumerated monomial universe. -/
theorem residualRank_le_length {n degree : ℕ} (residual : CMvPolynomial n F) :
    residualRank degree residual ≤ (boundedMonomials n degree).length := by
  unfold residualRank
  split
  · exact Nat.zero_le _
  · exact monomialRank_le_length _

/-- The mathematical graded-lex leading term is the monomial and coefficient
returned by the executable search. -/
theorem degLex_leadingTerm_eq_of_leadingTerm? {n : ℕ}
    {p : CMvPolynomial n F} {monomial : CMvMonomial n} {coefficient : F}
    (hterm : leadingTerm? p = some (monomial, coefficient)) :
    MonomialOrder.degLex.leadingTerm (fromCMvPolynomial p) =
      MvPolynomial.monomial monomial.toFinsupp coefficient := by
  unfold MonomialOrder.leadingTerm MonomialOrder.leadingCoeff
  rw [leadingTerm?_degree hterm, CPoly.coeff_eq,
    CMvMonomial.ofFinsupp_toFinsupp, leadingTerm?_coeff hterm]

/-- Componentwise monomial division followed by multiplication recovers the
original monomial whenever the divisor exponents are bounded coordinatewise. -/
theorem monomial_div_add_cancel {n : ℕ} (a b : CMvMonomial n)
    (h : ∀ i, b.get i ≤ a.get i) :
    a / b + b = a := by
  apply CMvMonomial.ext
  intro i hi
  change (Vector.zipWith Nat.add (Vector.zipWith Nat.sub a b) b)[i] = a[i]
  erw [Vector.getElem_zipWith, Vector.getElem_zipWith]
  exact Nat.sub_add_cancel (h ⟨i, hi⟩)

variable [BEq F] [LawfulBEq F]

/-- The multiple subtracted by a successful step has the same graded-lex
leading term as the current residual. -/
theorem divisionStep_subtrahend_leadingTerm {n : ℕ}
    {divisor residual : CMvPolynomial n F}
    {remainderMonomial divisorMonomial : CMvMonomial n}
    {remainderCoefficient divisorCoefficient : F}
    (hremainder :
      leadingTerm? residual = some (remainderMonomial, remainderCoefficient))
    (hdivisor :
      leadingTerm? divisor = some (divisorMonomial, divisorCoefficient))
    (hdivides : ∀ i, divisorMonomial.get i ≤ remainderMonomial.get i) :
    let term := CMvPolynomial.monomial
      (remainderMonomial / divisorMonomial)
      (remainderCoefficient / divisorCoefficient)
    MonomialOrder.degLex.leadingTerm
        (fromCMvPolynomial (term * divisor)) =
      MonomialOrder.degLex.leadingTerm (fromCMvPolynomial residual) := by
  dsimp only
  rw [CPoly.map_mul, CMvPolynomial.fromCMvPolynomial_monomial,
    MonomialOrder.leadingTerm_mul,
    MonomialOrder.leadingTerm_monomial,
    degLex_leadingTerm_eq_of_leadingTerm? hdivisor,
    degLex_leadingTerm_eq_of_leadingTerm? hremainder,
    MvPolynomial.monomial_mul]
  have hmonomial := monomial_div_add_cancel remainderMonomial divisorMonomial hdivides
  have htoFinsupp :
      (remainderMonomial / divisorMonomial).toFinsupp +
          divisorMonomial.toFinsupp =
        remainderMonomial.toFinsupp := by
    ext i
    change (remainderMonomial / divisorMonomial).get i +
      divisorMonomial.get i = remainderMonomial.get i
    have hcoordinate :
        (remainderMonomial / divisorMonomial).get i =
          remainderMonomial.get i - divisorMonomial.get i := by
      change (Vector.zipWith Nat.sub remainderMonomial divisorMonomial).get i =
        remainderMonomial.get i - divisorMonomial.get i
      exact Vector.getElem_zipWith i.isLt
    rw [hcoordinate, Nat.sub_add_cancel (hdivides i)]
  rw [htoFinsupp]
  congr 1
  exact div_mul_cancel₀ remainderCoefficient
    (leadingTerm?_coefficient_ne_zero hdivisor)

omit [BEq F] [LawfulBEq F] in
/-- Subtracting a polynomial with the same leading term either produces zero
or strictly lowers graded-lex degree. -/
theorem degLex_degree_sub_lt_or_eq_zero_of_leadingTerm_eq {n : ℕ}
    {f g : MvPolynomial (Fin n) F}
    (hleading :
      MonomialOrder.degLex.leadingTerm g =
        MonomialOrder.degLex.leadingTerm f) :
    MonomialOrder.degLex.degree (f - g) ≺[MonomialOrder.degLex]
        MonomialOrder.degLex.degree f ∨
      f - g = 0 := by
  let order := MonomialOrder.degLex (σ := Fin n)
  by_cases hzero : f - g = 0
  · exact Or.inr hzero
  · left
    have hleadingData :
        order.leadingCoeff g = order.leadingCoeff f ∧
          order.degree g = order.degree f :=
      order.leadingTerm_eq_leadingTerm_iff.mp hleading
    have hle :
        order.toSyn (order.degree (f - g)) ≤ order.toSyn (order.degree f) := by
      apply order.degree_sub_le.trans
      simp [hleadingData.2]
    apply lt_of_le_of_ne hle
    intro hequal
    have hdegreeEqual :
        order.degree (f - g) = order.degree f :=
      order.toSyn.injective hequal
    have hcoefficientNonzero :
        (f - g).coeff (order.degree (f - g)) ≠ 0 :=
      order.coeff_degree_ne_zero_iff.mpr hzero
    apply hcoefficientNonzero
    rw [hdegreeEqual, MvPolynomial.coeff_sub]
    nth_rewrite 2 [← hleadingData.2]
    change order.leadingCoeff f - order.leadingCoeff g = 0
    rw [hleadingData.1]
    exact sub_self _

/-- Every successful executable step strictly lowers the residual in the
well-founded graded-lex order with zero represented by bottom. -/
theorem divisionStep?_withBotDegree_lt {n : ℕ}
    {divisor : CMvPolynomial n F} {state next : DivisionState n (F := F)}
    (hstep : divisionStep? divisor state = some next) :
    MonomialOrder.degLex.withBotDegree (fromCMvPolynomial next.residual)
      ≺'[MonomialOrder.degLex]
    MonomialOrder.degLex.withBotDegree (fromCMvPolynomial state.residual) := by
  unfold divisionStep? at hstep
  split at hstep <;>
    try simp only [dite_eq_ite, Option.ite_none_right_eq_some,
      Option.some.injEq, reduceCtorEq] at hstep
  rename_i remainderTerm divisorTerm hremainder hdivisor
  rcases hstep with ⟨hdivides, rfl⟩
  dsimp only
  rw [MonomialOrder.withBotDegree_lt_withBotDegree_iff]
  have hleading := divisionStep_subtrahend_leadingTerm
    hremainder hdivisor hdivides
  have hdecrease :=
    degLex_degree_sub_lt_or_eq_zero_of_leadingTerm_eq hleading
  rw [show fromCMvPolynomial
      (state.residual -
        CMvPolynomial.monomial
          (remainderTerm.1 / divisorTerm.1)
          (remainderTerm.2 / divisorTerm.2) * divisor) =
      fromCMvPolynomial state.residual -
        fromCMvPolynomial
          (CMvPolynomial.monomial
            (remainderTerm.1 / divisorTerm.1)
            (remainderTerm.2 / divisorTerm.2) * divisor) from
      CPoly.map_sub _ _]
  rcases hdecrease with hdecrease | hzero
  · exact Or.inl hdecrease
  · exact Or.inr ⟨hzero, by
      intro hresidualMap
      have hresidual : state.residual = 0 := by
        apply fromCMvPolynomial_injective
        simpa using hresidualMap
      rw [hresidual] at hremainder
      unfold leadingTerm? at hremainder
      rw [Lawful.zero_eq_zero] at hremainder
      change List.argmax (gradedLexKey ∘ Prod.fst)
        ((0 : Unlawful n F).toList) = some remainderTerm at hremainder
      rw [Unlawful.zero_eq_empty] at hremainder
      have hempty : (∅ : Unlawful n F).toList = [] :=
        Std.ExtTreeMap.toList_eq_nil_iff.mpr rfl
      rw [hempty] at hremainder
      rw [List.argmax_nil] at hremainder
      cases hremainder⟩

/-- A successful reduction step never increases ordinary total degree. -/
theorem divisionStep?_totalDegree_le {n : ℕ}
    {divisor : CMvPolynomial n F} {state next : DivisionState n (F := F)}
    (hstep : divisionStep? divisor state = some next) :
    next.residual.totalDegree ≤ state.residual.totalDegree := by
  have hdecrease := divisionStep?_withBotDegree_lt hstep
  rw [MonomialOrder.withBotDegree_lt_withBotDegree_iff] at hdecrease
  rcases hdecrease with hdegree | ⟨hzero, _⟩
  · calc
      next.residual.totalDegree =
          (fromCMvPolynomial next.residual).totalDegree :=
        CPoly.totalDegree_equiv (S := F)
      _ ≤ (fromCMvPolynomial state.residual).totalDegree :=
        MvPolynomial.degLex_totalDegree_monotone (le_of_lt hdegree)
      _ = state.residual.totalDegree :=
        (CPoly.totalDegree_equiv (S := F)).symm
  · have hnext : next.residual = 0 := by
      apply fromCMvPolynomial_injective
      simpa using hzero
    rw [hnext]
    rw [CPoly.totalDegree_equiv (S := F), CPoly.map_zero,
      MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _

/-- The executable leading-term search is empty exactly for the zero
polynomial. -/
theorem leadingTerm?_eq_none_iff {n : ℕ} (p : CMvPolynomial n F) :
    leadingTerm? p = none ↔ p = 0 := by
  rw [leadingTerm?, List.argmax_eq_none,
    Std.ExtTreeMap.toList_eq_nil_iff]
  constructor
  · intro h
    apply CMvPolynomial.ext p 0
    intro monomial
    simp [CMvPolynomial.coeff, h]
  · rintro rfl
    change (0 : Unlawful n F) = (∅ : Unlawful n F)
    exact Unlawful.zero_eq_empty

/-- On a degree-bounded state, every successful executable step strictly
lowers the finite residual rank. -/
theorem divisionStep?_residualRank_lt {n degree : ℕ}
    {divisor : CMvPolynomial n F} {state next : DivisionState n (F := F)}
    (hdegree : state.residual.totalDegree ≤ degree)
    (hstep : divisionStep? divisor state = some next) :
    residualRank degree next.residual < residualRank degree state.residual := by
  cases hcurrent : leadingTerm? state.residual with
  | none =>
      unfold divisionStep? at hstep
      rw [hcurrent] at hstep
      simp at hstep
  | some current =>
      have hcurrentMem : current.1 ∈ boundedMonomials n degree := by
        rw [mem_boundedMonomials_iff_totalDegree_le,
          leadingTerm?_totalDegree hcurrent]
        exact hdegree
      cases hnext : leadingTerm? next.residual with
      | none =>
          simp only [residualRank, hcurrent, hnext]
          exact monomialRank_pos hcurrentMem
      | some nextTerm =>
          simp only [residualRank, hcurrent, hnext]
          apply monomialRank_lt hcurrentMem
          rw [gradedLexKey_lt_iff_degLex]
          have hdecrease := divisionStep?_withBotDegree_lt hstep
          rw [MonomialOrder.withBotDegree_lt_withBotDegree_iff] at hdecrease
          rcases hdecrease with hdecrease | ⟨hzero, _⟩
          · simpa [leadingTerm?_degree hnext,
              leadingTerm?_degree hcurrent] using hdecrease
          · have hnextZero : next.residual = 0 := by
              apply fromCMvPolynomial_injective
              simpa using hzero
            have hnone := (leadingTerm?_eq_none_iff next.residual).2 hnextZero
            rw [hnext] at hnone
            simp at hnone

/-- A successful reduction step preserves the decomposition represented by
the division state. -/
theorem divisionStep?_invariant {n : ℕ} {divisor : CMvPolynomial n F}
    {state next : DivisionState n (F := F)}
    (hstep : divisionStep? divisor state = some next) :
    next.quotient * divisor + next.residual =
      state.quotient * divisor + state.residual := by
  unfold divisionStep? at hstep
  split at hstep <;>
    try simp only [dite_eq_ite, Option.ite_none_right_eq_some,
      Option.some.injEq, reduceCtorEq] at hstep
  rename_i remainderTerm divisorTerm hremainder hdivisor
  rcases hstep with ⟨hdivides, rfl⟩
  dsimp
  ring

/-- Any run with more fuel than the residual's finite rank reaches a state
where no further leading-term reduction is available. -/
theorem divisionLoop_step_eq_none_of_rank_lt_fuel {n degree fuel : ℕ}
    (divisor : CMvPolynomial n F) (state : DivisionState n (F := F))
    (hdegree : state.residual.totalDegree ≤ degree)
    (hfuel : residualRank degree state.residual < fuel) :
    divisionStep? divisor (divisionLoop divisor fuel state) = none := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      rw [divisionLoop]
      cases hstep : divisionStep? divisor state with
      | none => exact hstep
      | some next =>
          apply ih next
          · exact (divisionStep?_totalDegree_le hstep).trans hdegree
          · have hrank := divisionStep?_residualRank_lt hdegree hstep
            omega

/-- The concrete enumerated fuel used by exact division always reaches a
state where no further leading-term reduction is available. -/
theorem initialDivisionLoop_step_eq_none {n : ℕ}
    (dividend divisor : CMvPolynomial n F) :
    divisionStep? divisor
      (divisionLoop divisor (divisionFuel dividend)
        { quotient := 0, residual := dividend }) = none := by
  apply divisionLoop_step_eq_none_of_rank_lt_fuel
    (degree := dividend.totalDegree)
  · exact le_rfl
  · have hbound := residualRank_le_length
      (degree := dividend.totalDegree) dividend
    simp only [divisionFuel]
    omega

/-- A nonzero residual which is a multiple of a nonzero divisor always admits
another leading-term reduction step. -/
theorem divisionStep?_ne_none_of_eq_mul {n : ℕ}
    {divisor multiplier residual accumulator : CMvPolynomial n F}
    (hresidual : residual = multiplier * divisor)
    (hresidualNe : residual ≠ 0) :
    divisionStep? divisor { quotient := accumulator, residual := residual } ≠ none := by
  have hmultiplierNe : multiplier ≠ 0 := by
    intro hzero
    apply hresidualNe
    simp [hresidual, hzero]
  have hdivisorNe : divisor ≠ 0 := by
    intro hzero
    apply hresidualNe
    simp [hresidual, hzero]
  have hmultiplierSome : leadingTerm? multiplier ≠ none := by
    intro hnone
    exact hmultiplierNe ((leadingTerm?_eq_none_iff multiplier).mp hnone)
  have hdivisorSome : leadingTerm? divisor ≠ none := by
    intro hnone
    exact hdivisorNe ((leadingTerm?_eq_none_iff divisor).mp hnone)
  have hresidualSome : leadingTerm? residual ≠ none := by
    intro hnone
    exact hresidualNe ((leadingTerm?_eq_none_iff residual).mp hnone)
  obtain ⟨multiplierTerm, hmultiplier⟩ :=
    Option.ne_none_iff_exists'.mp hmultiplierSome
  obtain ⟨divisorTerm, hdivisor⟩ :=
    Option.ne_none_iff_exists'.mp hdivisorSome
  obtain ⟨residualTerm, hleadingResidual⟩ :=
    Option.ne_none_iff_exists'.mp hresidualSome
  have hmapMultiplierNe : fromCMvPolynomial multiplier ≠ 0 := by
    intro hzero
    apply hmultiplierNe
    apply fromCMvPolynomial_injective
    simpa using hzero
  have hmapDivisorNe : fromCMvPolynomial divisor ≠ 0 := by
    intro hzero
    apply hdivisorNe
    apply fromCMvPolynomial_injective
    simpa using hzero
  have hleadingMonomial : residualTerm.1.toFinsupp =
      multiplierTerm.1.toFinsupp + divisorTerm.1.toFinsupp := by
    calc
      residualTerm.1.toFinsupp = MonomialOrder.degLex.degree
          (fromCMvPolynomial residual) :=
        (leadingTerm?_degree hleadingResidual).symm
      _ = MonomialOrder.degLex.degree
          (fromCMvPolynomial (multiplier * divisor)) := by rw [hresidual]
      _ = MonomialOrder.degLex.degree
          (fromCMvPolynomial multiplier * fromCMvPolynomial divisor) := by
        rw [CPoly.map_mul]
      _ = MonomialOrder.degLex.degree (fromCMvPolynomial multiplier) +
          MonomialOrder.degLex.degree (fromCMvPolynomial divisor) :=
        MonomialOrder.degree_mul hmapMultiplierNe hmapDivisorNe
      _ = multiplierTerm.1.toFinsupp + divisorTerm.1.toFinsupp := by
        rw [leadingTerm?_degree hmultiplier, leadingTerm?_degree hdivisor]
  have hdivides : ∀ i, divisorTerm.1.get i ≤ residualTerm.1.get i := by
    intro i
    change divisorTerm.1.toFinsupp i ≤ residualTerm.1.toFinsupp i
    rw [hleadingMonomial, Finsupp.add_apply]
    omega
  unfold divisionStep?
  rw [hleadingResidual, hdivisor]
  simp only
  split
  · simp
  · exact fun _ => ‹¬ ∀ i, divisorTerm.1.get i ≤ residualTerm.1.get i›
      hdivides

/-- Every bounded run preserves quotient-times-divisor plus residual. -/
theorem divisionLoop_invariant {n : ℕ} (divisor : CMvPolynomial n F)
    (fuel : ℕ) (state : DivisionState n (F := F)) :
    (divisionLoop divisor fuel state).quotient * divisor +
        (divisionLoop divisor fuel state).residual =
      state.quotient * divisor + state.residual := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [divisionLoop]
      cases hstep : divisionStep? divisor state with
      | none => rfl
      | some next =>
          rw [ih]
          exact divisionStep?_invariant hstep

/-- The run used by checked exact division always represents the original
dividend. -/
theorem initialDivisionLoop_invariant {n : ℕ}
    (dividend divisor : CMvPolynomial n F) :
    let state := divisionLoop divisor (divisionFuel dividend)
      { quotient := 0, residual := dividend }
    state.quotient * divisor + state.residual = dividend := by
  simpa using divisionLoop_invariant divisor (divisionFuel dividend)
    { quotient := 0, residual := dividend }

/-- When the dividend is a multiple of the divisor, the fuel-bounded run has
zero residual. -/
theorem initialDivisionLoop_residual_eq_zero_of_eq_mul {n : ℕ}
    {dividend divisor multiplier : CMvPolynomial n F}
    (hdividend : multiplier * divisor = dividend) :
    (divisionLoop divisor (divisionFuel dividend)
      { quotient := 0, residual := dividend }).residual = 0 := by
  let state := divisionLoop divisor (divisionFuel dividend)
    { quotient := 0, residual := dividend }
  have hnormal : divisionStep? divisor state = none := by
    exact initialDivisionLoop_step_eq_none dividend divisor
  have hinvariant : state.quotient * divisor + state.residual = dividend := by
    exact initialDivisionLoop_invariant dividend divisor
  by_contra hresidualNe
  have hresidual : state.residual =
      (multiplier - state.quotient) * divisor := by
    calc
      state.residual = dividend - state.quotient * divisor := by
        rw [← hinvariant]
        ring
      _ = multiplier * divisor - state.quotient * divisor := by
        rw [hdividend]
      _ = (multiplier - state.quotient) * divisor := by ring
  exact (divisionStep?_ne_none_of_eq_mul
    (accumulator := state.quotient) hresidual hresidualNe) hnormal

variable [DecidableEq F]

/-- Completeness of checked exact division over a nonzero divisor: whenever
an exact quotient identity holds, the executable reducer returns that unique
quotient. -/
theorem checkedExactQuotient?_complete {n : ℕ}
    {dividend divisor quotient : CMvPolynomial n F}
    (hdivisor : divisor ≠ 0) (hquotient : quotient * divisor = dividend) :
    checkedExactQuotient? dividend divisor = some quotient := by
  let state := divisionLoop divisor (divisionFuel dividend)
    { quotient := 0, residual := dividend }
  have hresidual : state.residual = 0 :=
    initialDivisionLoop_residual_eq_zero_of_eq_mul hquotient
  have hinvariant : state.quotient * divisor + state.residual = dividend :=
    initialDivisionLoop_invariant dividend divisor
  have hstateQuotient : state.quotient * divisor = dividend := by
    simpa [hresidual] using hinvariant
  have hequal : state.quotient = quotient := by
    apply fromCMvPolynomial_injective
    apply mul_right_cancel₀ (b := fromCMvPolynomial divisor)
    · intro hzero
      apply hdivisor
      apply fromCMvPolynomial_injective
      simpa using hzero
    · rw [← CPoly.map_mul, ← CPoly.map_mul,
        hstateQuotient, hquotient]
  unfold checkedExactQuotient?
  change (if state.quotient * divisor = dividend then some state.quotient else none) =
    some quotient
  rw [if_pos hstateQuotient, hequal]

/-- For a nonzero divisor, executable exact division returns a given quotient
exactly when its product is the dividend. -/
theorem checkedExactQuotient?_eq_some_iff {n : ℕ}
    {dividend divisor quotient : CMvPolynomial n F} (hdivisor : divisor ≠ 0) :
    checkedExactQuotient? dividend divisor = some quotient ↔
      quotient * divisor = dividend :=
  ⟨checkedExactQuotient?_sound, checkedExactQuotient?_complete hdivisor⟩

/-- Divisibility by a nonzero divisor guarantees executable success. -/
theorem checkedExactQuotient?_isSome_of_dvd {n : ℕ}
    {dividend divisor : CMvPolynomial n F} (hdivisor : divisor ≠ 0)
    (hdivides : divisor ∣ dividend) :
    ∃ quotient, checkedExactQuotient? dividend divisor = some quotient := by
  obtain ⟨quotient, rfl⟩ := hdivides
  exact ⟨quotient, checkedExactQuotient?_complete hdivisor (by ring)⟩

/-- The computed Canny quotient succeeds once its determinant identity is
available and the computed extraneous determinant is nonzero. -/
theorem macaulayQuotient?_complete_of_identity {n : ℕ}
    {system : Fin n → CMvPolynomial n F} {quotient : Parameters n F}
    (hfactor : extraneousFactor system ≠ 0)
    (hidentity : quotient * extraneousFactor system = characteristic system) :
    macaulayQuotient? system = some quotient := by
  unfold macaulayQuotient?
  simp only [hfactor, ↓reduceIte]
  exact checkedExactQuotient?_complete hfactor hidentity

/-- Complete success characterization for the computed Canny division. -/
theorem macaulayQuotient?_eq_some_iff {n : ℕ}
    {system : Fin n → CMvPolynomial n F} {quotient : Parameters n F} :
    macaulayQuotient? system = some quotient ↔
      extraneousFactor system ≠ 0 ∧
        quotient * extraneousFactor system = characteristic system := by
  constructor
  · intro hquotient
    exact ⟨macaulayQuotient?_extraneousFactor_ne_zero hquotient,
      macaulayQuotient?_sound hquotient⟩
  · rintro ⟨hfactor, hidentity⟩
    exact macaulayQuotient?_complete_of_identity hfactor hidentity

/-- Canny's determinant divisibility and nonzero extraneous minor guarantee
that the computed Macaulay quotient succeeds. -/
theorem macaulayQuotient?_isSome_of_dvd {n : ℕ}
    {system : Fin n → CMvPolynomial n F}
    (hfactor : extraneousFactor system ≠ 0)
    (hdivides : extraneousFactor system ∣ characteristic system) :
    ∃ quotient, macaulayQuotient? system = some quotient := by
  obtain ⟨quotient, hidentity⟩ := hdivides
  exact ⟨quotient, macaulayQuotient?_complete_of_identity hfactor
    (by simpa only [mul_comm] using hidentity.symm)⟩

end ArkLib.Rojas.Producer.MacaulayQuotient
