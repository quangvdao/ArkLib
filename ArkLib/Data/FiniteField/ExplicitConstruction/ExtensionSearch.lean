/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

import Mathlib.Algebra.CharP.CharAndCard

public import ArkLib.Data.FiniteField.ExplicitConstruction.SuppliedField
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Data.List.Find
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Data.Nat.Log
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Exhaustive construction of a least-degree finite-field extension

The only exhaustive enumeration in this module is the bounded list of monic
polynomials permitted by the decoder's field-construction argument.  The
coefficient field is represented by a stored cardinality and mutually inverse
computable indexing functions, so execution never asks `Fintype.card` to
enumerate the current field.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction

open CompPoly CompPoly.CPolynomial

/-- Every positive degree occurs as the degree of a monic irreducible polynomial
over a finite field. This theorem supplies only the completeness proof for the
executed finite search; it does not select the returned modulus. -/
theorem exists_monic_irreducible_degree (E : Type*) [Field E] [Finite E]
    (degree : Nat) (hd : 0 < degree) :
    ∃ f : Polynomial E, f.Monic ∧ Irreducible f ∧ f.natDegree = degree := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists E
  let : CharP E p := hp
  let : Fact p.Prime := ⟨CharP.char_is_prime E p⟩
  let : NeZero degree := ⟨hd.ne'⟩
  let L := FiniteField.Extension E p degree
  obtain ⟨a, ha⟩ := Field.exists_primitive_element_of_finite_top E L
  have hi : IsIntegral E a := Algebra.IsIntegral.isIntegral a
  refine ⟨minpoly E a, minpoly.monic hi, minpoly.irreducible hi, ?_⟩
  rw [← IntermediateField.adjoin.finrank hi, ha, IntermediateField.finrank_top']
  exact FiniteField.finrank_extension E p degree

/-- All length-`degree` coefficient vectors over the indexed current field. -/
def coefficientVectors {E : Type*} (index : FiniteIndex E) : Nat → List (List E)
  | 0 => [[]]
  | degree + 1 => index.values.flatMap fun a =>
      (coefficientVectors index degree).map (a :: ·)

@[simp] theorem mem_coefficientVectors_iff {E : Type*} (index : FiniteIndex E)
    (coefficients : List E) : ∀ degree,
    coefficients ∈ coefficientVectors index degree ↔ coefficients.length = degree := by
  intro degree
  induction degree generalizing coefficients with
  | zero => simp [coefficientVectors]
  | succ degree ih =>
      simp only [coefficientVectors, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨a, _, tail, htail, rfl⟩
        simp [(ih tail).mp htail]
      · intro hlength
        cases coefficients with
        | nil => simp at hlength
        | cons a tail =>
          have htail : tail.length = degree := by simpa using hlength
          exact ⟨a, index.mem_values a, tail, (ih tail).mpr htail, rfl⟩

/-- A monic stored polynomial with the supplied little-endian lower coefficients. -/
def monicPolynomial {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (coefficients : List E) : CPolynomial E :=
  X ^ coefficients.length +
    ∑ i : Fin coefficients.length, C coefficients[i] * X ^ (i : Nat)

theorem degree_lower_lt {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (coefficients : List E) :
    (∑ i : Fin coefficients.length,
      Polynomial.C coefficients[i] * Polynomial.X ^ (i : Nat) : Polynomial E).degree <
        coefficients.length := by
  exact Polynomial.degree_sum_fin_lt _

theorem toPoly_monicPolynomial {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (coefficients : List E) :
    (monicPolynomial coefficients).toPoly =
      Polynomial.X ^ coefficients.length +
        ∑ i : Fin coefficients.length,
          Polynomial.C coefficients[i] * Polynomial.X ^ (i : Nat) := by
  simp [monicPolynomial, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.toPoly_sum, CPolynomial.toPoly_mul, CPolynomial.C_toPoly,
    CPolynomial.X_toPoly]

theorem monic_monicPolynomial {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (coefficients : List E) : (monicPolynomial coefficients).monic := by
  rw [CPolynomial.monic_toPoly_iff, toPoly_monicPolynomial]
  exact Polynomial.monic_X_pow_add (degree_lower_lt coefficients)

theorem coeff_monicPolynomial {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (coefficients : List E) (n : Nat) :
    (monicPolynomial coefficients).coeff n =
      if h : n < coefficients.length then coefficients[n] else
        if n = coefficients.length then 1 else 0 := by
  rw [CPolynomial.coeff_toPoly, toPoly_monicPolynomial, Polynomial.coeff_add]
  have hsum :
      (∑ i : Fin coefficients.length,
        Polynomial.C coefficients[i] * Polynomial.X ^ (i : Nat) : Polynomial E).coeff n =
      ∑ i : Fin coefficients.length,
        (Polynomial.C coefficients[i] * Polynomial.X ^ (i : Nat) : Polynomial E).coeff n := by
    exact Polynomial.finsetSum_coeff Finset.univ
      (fun i : Fin coefficients.length =>
        Polynomial.C coefficients[i] * Polynomial.X ^ (i : Nat)) n
  rw [hsum]
  by_cases hn : n < coefficients.length
  · simp only [hn, dite_true, Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt hn),
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, zero_add]
    rw [Finset.sum_eq_single ⟨n, hn⟩]
    · simp
    · intro i _ hine
      have hneNat : n ≠ (i : Nat) := fun heq => hine (Fin.ext heq.symm)
      simp only [if_neg hneNat]
      simp
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  · simp only [hn, dite_false, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases heq : n = coefficients.length
    · subst n
      have hzero : (∑ i : Fin coefficients.length,
          coefficients[i] * if coefficients.length = (i : Nat) then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [if_neg (Ne.symm (Nat.ne_of_lt i.isLt))]
        simp
      rw [hzero]
      simp
    · have hlarge : coefficients.length < n :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_gt hn) (Ne.symm heq)
      simp only [heq, if_false, zero_add]
      apply Finset.sum_eq_zero
      intro i _
      have hne : n ≠ (i : Nat) := Nat.ne_of_gt (i.isLt.trans hlarge)
      simp only [if_neg hne]
      simp

@[simp] theorem natDegree_monicPolynomial {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (coefficients : List E) :
    (monicPolynomial coefficients).natDegree = coefficients.length := by
  rw [CPolynomial.natDegree_toPoly, toPoly_monicPolynomial]
  have h := Polynomial.natDegree_add_eq_left_of_degree_lt (p := Polynomial.X ^ coefficients.length)
    (q := ∑ i : Fin coefficients.length,
      Polynomial.C coefficients[i] * Polynomial.X ^ (i : Nat)) (by
        rw [Polynomial.degree_X_pow]
        exact degree_lower_lt coefficients)
  simpa using h

/-- Complete enumeration of monic polynomials of one fixed degree. -/
def monicPolynomials {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (degree : Nat) :
    List (CPolynomial E) :=
  (coefficientVectors index degree).map monicPolynomial

theorem monic_of_mem_monicPolynomials {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) {degree : Nat} {p : CPolynomial E}
    (hp : p ∈ monicPolynomials index degree) : p.monic := by
  obtain ⟨coefficients, _, rfl⟩ := List.mem_map.mp hp
  exact monic_monicPolynomial coefficients

theorem natDegree_of_mem_monicPolynomials {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) {degree : Nat} {p : CPolynomial E}
    (hp : p ∈ monicPolynomials index degree) : p.natDegree = degree := by
  obtain ⟨coefficients, hcoefficients, rfl⟩ := List.mem_map.mp hp
  rw [natDegree_monicPolynomial]
  exact (mem_coefficientVectors_iff index coefficients degree).mp hcoefficients

theorem mem_monicPolynomials {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E)
    {p : CPolynomial E} (hp : p.monic) {degree : Nat}
    (hdegree : p.natDegree = degree) :
    p ∈ monicPolynomials index degree := by
  let coefficients := (List.range degree).map p.coeff
  have hlength : coefficients.length = degree := by simp [coefficients]
  rw [monicPolynomials, List.mem_map]
  refine ⟨coefficients, (mem_coefficientVectors_iff index coefficients degree).mpr hlength, ?_⟩
  rw [CPolynomial.eq_iff_coeff]
  intro n
  rw [coeff_monicPolynomial]
  by_cases hn : n < degree
  · have hnc : n < coefficients.length := by simpa [hlength] using hn
    rw [dif_pos hnc]
    simp [coefficients]
  · have hle : degree ≤ n := Nat.le_of_not_gt hn
    by_cases heq : n = degree
    · subst n
      have hpc : p.coeff p.natDegree = 1 := by
        rw [CPolynomial.coeff_toPoly]
        simpa [← CPolynomial.natDegree_toPoly] using
          ((CPolynomial.monic_toPoly_iff p).mp hp).coeff_natDegree
      simpa [hlength, coefficients, hdegree] using hpc.symm
    · have hlt : degree < n := lt_of_le_of_ne hle (Ne.symm heq)
      have hpzero : p.coeff n = 0 := by
        rw [CPolynomial.coeff_toPoly]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rwa [← CPolynomial.natDegree_toPoly, hdegree]
      simp [hlength, hn, heq, hpzero]

/-- Candidate proper monic divisors sufficient for the standard irreducibility criterion. -/
def properMonicDivisors {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (degree : Nat) :
    List (CPolynomial E) :=
  (List.range (degree / 2)).flatMap fun offset => monicPolynomials index (offset + 1)

theorem properties_of_mem_properMonicDivisors {E : Type*}
    [Field E] [BEq E] [LawfulBEq E] (index : FiniteIndex E)
    {degree : Nat} {p : CPolynomial E} (hp : p ∈ properMonicDivisors index degree) :
    p.monic ∧ 0 < p.natDegree ∧ p.natDegree ≤ degree / 2 := by
  obtain ⟨offset, hoffset, hp⟩ := List.mem_flatMap.mp hp
  have hdegree := natDegree_of_mem_monicPolynomials index hp
  refine ⟨monic_of_mem_monicPolynomials index hp, hdegree ▸ Nat.zero_lt_succ offset, ?_⟩
  rw [hdegree]
  exact List.mem_range.mp hoffset

theorem mem_properMonicDivisors {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E)
    {p : CPolynomial E} (hp : p.monic) {degree : Nat}
    (hpos : 0 < p.natDegree) (hle : p.natDegree ≤ degree / 2) :
    p ∈ properMonicDivisors index degree := by
  rw [properMonicDivisors, List.mem_flatMap]
  refine ⟨p.natDegree - 1, ?_, ?_⟩
  · simp only [List.mem_range]
    omega
  · have hdegree : p.natDegree - 1 + 1 = p.natDegree := by omega
    simpa [hdegree] using mem_monicPolynomials index hp rfl

/-- Executable proper-divisor test. Every divisor candidate is monic. -/
def hasProperMonicDivisor {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (p : CPolynomial E) : Bool :=
  (properMonicDivisors index p.natDegree).any fun q =>
    if hq : q.monic then
      letI : Fact q.monic := ⟨hq⟩
      p.modByMonic q == 0
    else false

theorem hasProperMonicDivisor_eq_true_iff {E : Type*}
    [Field E] [BEq E] [LawfulBEq E] (index : FiniteIndex E) (p : CPolynomial E) :
    hasProperMonicDivisor index p = true ↔
      ∃ q ∈ properMonicDivisors index p.natDegree, q.toPoly ∣ p.toPoly := by
  rw [hasProperMonicDivisor, List.any_eq_true]
  constructor
  · rintro ⟨q, hqmem, htest⟩
    have hq := (properties_of_mem_properMonicDivisors index hqmem).1
    simp only [dif_pos hq, beq_iff_eq] at htest
    refine ⟨q, hqmem, ?_⟩
    have hsem := congrArg CPolynomial.toPoly htest
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic p q hq,
      CPolynomial.toPoly_zero] at hsem
    exact (Polynomial.modByMonic_eq_zero_iff_dvd
      ((CPolynomial.monic_toPoly_iff q).mp hq)).mp hsem
  · rintro ⟨q, hqmem, hqdvd⟩
    refine ⟨q, hqmem, ?_⟩
    have hq := (properties_of_mem_properMonicDivisors index hqmem).1
    simp only [dif_pos hq, beq_iff_eq]
    apply CPolynomial.toPoly_injective
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic p q hq,
      CPolynomial.toPoly_zero]
    exact (Polynomial.modByMonic_eq_zero_iff_dvd
      ((CPolynomial.monic_toPoly_iff q).mp hq)).mpr hqdvd

/-- Verified executable irreducibility decision for positive-degree monic polynomials. -/
def irreducibleTest {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (p : CPolynomial E) : Bool :=
  p.monic && (p != 1) && !(hasProperMonicDivisor index p)

theorem irreducibleTest_eq_true_iff {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (p : CPolynomial E) :
    irreducibleTest index p = true ↔ p.monic ∧ Irreducible p.toPoly := by
  rw [irreducibleTest, Bool.and_eq_true, Bool.and_eq_true, bne_iff_ne]
  constructor
  · rintro ⟨⟨hpmonic, hpone⟩, hproperBool⟩
    refine ⟨hpmonic, ?_⟩
    have hproper : ¬∃ q ∈ properMonicDivisors index p.natDegree,
        q.toPoly ∣ p.toPoly := by
      intro h
      have htrue := (hasProperMonicDivisor_eq_true_iff index p).mpr h
      simp [htrue] at hproperBool
    have hpmonicPoly := (CPolynomial.monic_toPoly_iff p).mp hpmonic
    have hponePoly : p.toPoly ≠ 1 := by
      intro h
      apply hpone
      apply CPolynomial.toPoly_injective
      rw [CPolynomial.toPoly_one]
      exact h
    rw [hpmonicPoly.irreducible_iff_lt_natDegree_lt hponePoly]
    intro q hqmonic hqdegree hqdvd
    let qStored : CPolynomial E := ⟨q.toImpl, CPolynomial.Raw.isCanonical_toImpl q⟩
    have hqsem : qStored.toPoly = q := CPolynomial.toPoly_mk_toImpl q
    have hqStoredMonic : qStored.monic := by
      rw [CPolynomial.monic_toPoly_iff, hqsem]
      exact hqmonic
    have hqStoredDegree : qStored.natDegree = q.natDegree := by
      rw [CPolynomial.natDegree_toPoly, hqsem]
    have hpStoredDegree : p.toPoly.natDegree = p.natDegree :=
      (CPolynomial.natDegree_toPoly p).symm
    rw [hpStoredDegree] at hqdegree
    apply hproper
    refine ⟨qStored, mem_properMonicDivisors index hqStoredMonic
      (hqStoredDegree ▸ (Finset.mem_Ioc.mp hqdegree).1)
      (hqStoredDegree ▸ (Finset.mem_Ioc.mp hqdegree).2), ?_⟩
    rwa [hqsem]
  · rintro ⟨hpmonic, hp⟩
    have hpmonicPoly := (CPolynomial.monic_toPoly_iff p).mp hpmonic
    have hpone : p ≠ 1 := by
      intro h
      subst p
      rw [CPolynomial.toPoly_one] at hp
      exact hp.not_isUnit isUnit_one
    refine ⟨⟨hpmonic, hpone⟩, ?_⟩
    by_cases htest : hasProperMonicDivisor index p = true
    · have hexists := (hasProperMonicDivisor_eq_true_iff index p).mp htest
      obtain ⟨q, hqmem, hqdvd⟩ := hexists
      have hprops := properties_of_mem_properMonicDivisors index hqmem
      have hfalse := ((hpmonicPoly.irreducible_iff_lt_natDegree_lt (by
        intro h
        apply hpone
        apply CPolynomial.toPoly_injective
        rw [CPolynomial.toPoly_one]
        exact h)).mp hp) q.toPoly
          ((CPolynomial.monic_toPoly_iff q).mp hprops.1)
          (by
            apply Finset.mem_Ioc.mpr
            simpa [← CPolynomial.natDegree_toPoly] using hprops.2)
          hqdvd
      exact hfalse.elim
    · cases hvalue : hasProperMonicDivisor index p with
      | false => rfl
      | true => exact (htest hvalue).elim

/-- First successful monic irreducible candidate in the complete degree list. -/
def firstIrreducible? {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (degree : Nat) : Option (CPolynomial E) :=
  (monicPolynomials index degree).find? (irreducibleTest index)

theorem firstIrreducible?_sound {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) {degree : Nat} {p : CPolynomial E}
    (h : firstIrreducible? index degree = some p) :
    p.monic ∧ p.toPoly.natDegree = degree ∧ Irreducible p.toPoly := by
  have hmem : p ∈ monicPolynomials index degree :=
    List.mem_of_find?_eq_some h
  have htest : irreducibleTest index p = true := List.find?_some h
  have hirred := (irreducibleTest_eq_true_iff index p).mp htest
  refine ⟨hirred.1, ?_, hirred.2⟩
  simpa only [CPolynomial.natDegree_toPoly] using
    natDegree_of_mem_monicPolynomials index hmem

/-- Completeness of the executed list: positive-degree search cannot return failure. -/
theorem firstIrreducible?_ne_none {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) {degree : Nat} (hdegree : 0 < degree) :
    firstIrreducible? index degree ≠ none := by
  let _ : Finite E := Finite.of_equiv (Fin index.cardinality) index.equivFin
  obtain ⟨f, hfmonic, hfirred, hfdegree⟩ :=
    exists_monic_irreducible_degree E degree hdegree
  let p : CPolynomial E := ⟨f.toImpl, CPolynomial.Raw.isCanonical_toImpl f⟩
  have hpsem : p.toPoly = f := CPolynomial.toPoly_mk_toImpl f
  have hpmonic : p.monic := by
    rw [CPolynomial.monic_toPoly_iff, hpsem]
    exact hfmonic
  have hpdegree : p.natDegree = degree := by
    rw [CPolynomial.natDegree_toPoly, hpsem]
    exact hfdegree
  have hpmem : p ∈ monicPolynomials index degree :=
    mem_monicPolynomials index hpmonic hpdegree
  have hptest : irreducibleTest index p = true :=
    (irreducibleTest_eq_true_iff index p).mpr ⟨hpmonic, hpsem ▸ hfirred⟩
  intro hnone
  exact (List.find?_eq_none.mp hnone p hpmem) hptest

/-- Total executable first-success selection, justified by exhaustive-search completeness. -/
def firstIrreducible {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (degree : Nat) (hdegree : 0 < degree) : CPolynomial E :=
  (firstIrreducible? index degree).get
    (Option.isSome_iff_ne_none.mpr (firstIrreducible?_ne_none index hdegree))

theorem firstIrreducible_spec {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (degree : Nat) (hdegree : 0 < degree) :
    firstIrreducible? index degree = some (firstIrreducible index degree hdegree) := by
  exact (Option.some_get _).symm

theorem firstIrreducible_sound {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (degree : Nat) (hdegree : 0 < degree) :
    (firstIrreducible index degree hdegree).monic ∧
      (firstIrreducible index degree hdegree).toPoly.natDegree = degree ∧
      Irreducible (firstIrreducible index degree hdegree).toPoly :=
  firstIrreducible?_sound index (firstIrreducible_spec index degree hdegree)

/-- Candidates rejected before the first successful irreducibility test. -/
def searchTrace {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (degree : Nat) : List (CPolynomial E) :=
  (monicPolynomials index degree).takeWhile fun p => !(irreducibleTest index p)

theorem mem_searchTrace_not_irreducible {E : Type*}
    [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) {degree : Nat} {p : CPolynomial E}
    (hp : p ∈ searchTrace index degree) : ¬Irreducible p.toPoly := by
  rw [searchTrace] at hp
  have htest : irreducibleTest index p = false := by
    have := List.mem_takeWhile_imp
      (p := fun q : CPolynomial E => !(irreducibleTest index q)) hp
    simpa using this
  intro hirred
  have hmem : p ∈ monicPolynomials index degree :=
    (List.takeWhile_sublist (fun p => !(irreducibleTest index p))).subset hp
  have hmonic := monic_of_mem_monicPolynomials index hmem
  have : irreducibleTest index p = true :=
    (irreducibleTest_eq_true_iff index p).mpr ⟨hmonic, hirred⟩
  rw [this] at htest
  contradiction

/-- Least positive degree whose `q`-power is at least `B`. -/
def leastDegree (q B : Nat) : Nat :=
  max 1 (Nat.clog q B)

theorem leastDegree_spec {q B : Nat} (hq : 2 ≤ q) :
    0 < leastDegree q B ∧ B ≤ q ^ leastDegree q B ∧
      ∀ e, 0 < e → B ≤ q ^ e → leastDegree q B ≤ e := by
  have hq' : 1 < q := hq
  refine ⟨by simp [leastDegree], ?_, ?_⟩
  · exact (Nat.le_pow_clog hq' B).trans
      (Nat.pow_le_pow_right (by omega) (Nat.le_max_right 1 (Nat.clog q B)))
  · intro e he hsufficient
    rw [leastDegree, max_le_iff]
    exact ⟨he, (Nat.clog_le_iff_le_pow hq').mpr hsufficient⟩

/-- Executed trace returned by a successful least-degree modulus search. -/
structure SearchResult (E : Type*) [Field E] [BEq E] where
  requested : Nat
  baseCardinality : Nat
  degree : Nat
  modulus : CPolynomial E
  monic : modulus.monic
  irreducible : Irreducible modulus.toPoly
  degree_eq : modulus.toPoly.natDegree = degree
  sufficient : requested ≤ baseCardinality ^ degree
  least : ∀ e, 0 < e → requested ≤ baseCardinality ^ e → degree ≤ e

namespace SearchResult

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- The actual quotient field selected by the executed irreducibility search. -/
abbrev FieldType (result : SearchResult E) :=
  Carrier result.modulus

@[instance_reducible] instance (result : SearchResult E) : Field result.FieldType := by
  let _ : Fact result.modulus.monic := ⟨result.monic⟩
  let _ : Fact (Irreducible result.modulus.toPoly) := ⟨result.irreducible⟩
  infer_instance

/-- The coefficient-field embedding into the constructed quotient. -/
def embedding (result : SearchResult E) : E →+* result.FieldType := by
  let _ : Fact result.modulus.monic := ⟨result.monic⟩
  exact ExplicitConstruction.embedding result.modulus

instance (result : SearchResult E) : Algebra E result.FieldType :=
  result.embedding.toAlgebra

theorem embedding_injective (result : SearchResult E) :
    Function.Injective result.embedding := by
  let _ : Fact result.modulus.monic := ⟨result.monic⟩
  exact ExplicitConstruction.embedding_injective result.modulus
    (Polynomial.degree_pos_of_irreducible result.irreducible)

/-- The executable little-endian coordinate index of the constructed extension. -/
def coordinateIndex (result : SearchResult E) (index : FiniteIndex E)
    (_hcard : result.baseCardinality = index.cardinality) :
    Fin (index.cardinality ^ result.degree) ≃ result.FieldType := by
  let _ : Fact result.modulus.monic := ⟨result.monic⟩
  have hdegree : result.modulus.natDegree = result.degree := by
    simpa only [CPolynomial.natDegree_toPoly] using result.degree_eq
  exact (finCongr (congrArg (index.cardinality ^ ·) hdegree).symm).trans
    (polynomialBasisIndex result.modulus index)

/-- Allocate exactly the requested prefix from the constructed extension. -/
def centers (result : SearchResult E) (index : FiniteIndex E)
    (_hcard : result.baseCardinality = index.cardinality) : List result.FieldType := by
  let _ : Fact result.modulus.monic := ⟨result.monic⟩
  exact polynomialBasisPrefix result.modulus index result.requested

@[simp] theorem centers_length (result : SearchResult E) (index : FiniteIndex E)
    (hcard : result.baseCardinality = index.cardinality) :
    (result.centers index hcard).length = result.requested := by
    let _ : Fact result.modulus.monic := ⟨result.monic⟩
    exact polynomialBasisPrefix_length _ _ _

theorem centers_nodup (result : SearchResult E) (index : FiniteIndex E)
    (hcard : result.baseCardinality = index.cardinality) :
    (result.centers index hcard).Nodup := by
  let _ : Fact result.modulus.monic := ⟨result.monic⟩
  change (polynomialBasisPrefix result.modulus index result.requested).Nodup
  apply polynomialBasisPrefix_nodup
  have hdegree : result.modulus.natDegree = result.degree := by
    simpa only [CPolynomial.natDegree_toPoly] using result.degree_eq
  rw [hdegree]
  simpa [hcard] using result.sufficient

/-- Exact quotient cardinality, with the searched least degree. -/
theorem cardinality (result : SearchResult E) (index : FiniteIndex E)
    (_hcard : result.baseCardinality = index.cardinality) :
    Nat.card result.FieldType = index.cardinality ^ result.degree := by
  let _ : Fact result.modulus.monic := ⟨result.monic⟩
  rw [carrier_cardinality result.modulus index]
  have hdegree : result.modulus.natDegree = result.degree := by
    simpa only [CPolynomial.natDegree_toPoly] using result.degree_eq
  rw [hdegree]

/-- Exact vector-space dimension of the constructed extension. The proof uses
the executable coordinate cardinality and the standard finite-vector-space count. -/
theorem finrank (result : SearchResult E) (index : FiniteIndex E)
    (hcard : result.baseCardinality = index.cardinality) :
    Module.finrank E result.FieldType = result.degree := by
  let _ : Finite E := Finite.of_equiv (Fin index.cardinality) index.equivFin
  let _ : Finite result.FieldType :=
    Finite.of_equiv (Fin (index.cardinality ^ result.degree))
      (result.coordinateIndex index hcard)
  let _ : Module.Finite E result.FieldType := by
    let _ : Module.Finite E (Submodule.span E (Set.univ : Set result.FieldType)) :=
      Module.Finite.span_of_finite E Set.finite_univ
    exact Module.Finite.of_surjective
      (Submodule.subtype (Submodule.span E (Set.univ : Set result.FieldType)))
      (fun x => ⟨⟨x, by simp⟩, rfl⟩)
  have hE : Nat.card E = index.cardinality := by
    simpa using (Nat.card_congr index.equivFin).symm
  apply Nat.pow_right_injective index.one_lt_cardinality
  calc
    index.cardinality ^ Module.finrank E result.FieldType =
        Nat.card E ^ Module.finrank E result.FieldType := by
      rw [hE]
    _ = Nat.card result.FieldType := Module.natCard_eq_pow_finrank.symm
    _ = index.cardinality ^ result.degree := result.cardinality index hcard

/-- Inverse characteristic Frobenius in the constructed finite field. Unlike the
supplied-field preprocessing path, the positive-order extension is already in the
paper's bounded-size branch, so exponentiation by `|E'| / p` is executable here. -/
def inverseFrobenius (p : Nat) (result : SearchResult E) (index : FiniteIndex E)
    (a : result.FieldType) : result.FieldType :=
  a ^ ((index.cardinality ^ result.degree) / p)

/-- The cardinality exponent is the inverse of characteristic Frobenius on the
actual searched quotient. -/
theorem inverseFrobenius_pow (p : Nat) [Fact p.Prime] [CharP E p]
    (result : SearchResult E) (index : FiniteIndex E)
    (hcard : result.baseCardinality = index.cardinality) (a : result.FieldType) :
    result.inverseFrobenius p index a ^ p = a := by
  let _ : Finite result.FieldType :=
    Finite.of_equiv (Fin (index.cardinality ^ result.degree))
      (result.coordinateIndex index hcard)
  let _ : Fintype result.FieldType := Fintype.ofFinite result.FieldType
  let _ : Fact result.modulus.monic := ⟨result.monic⟩
  let _ : Fact (Irreducible result.modulus.toPoly) := ⟨result.irreducible⟩
  let _ : CharP result.FieldType p := carrierCharP result.modulus
  have hpChar : p ∣ ringChar result.FieldType := by
    rw [ringChar.eq result.FieldType p]
  have hpCard : p ∣ Fintype.card result.FieldType :=
    (prime_dvd_char_iff_dvd_card p).mp hpChar
  have hcardinality : Fintype.card result.FieldType =
      index.cardinality ^ result.degree := by
    rw [Fintype.card_eq_nat_card]
    exact result.cardinality index hcard
  rw [inverseFrobenius, ← pow_mul, Nat.div_mul_cancel (hcardinality ▸ hpCard)]
  rw [← hcardinality]
  exact FiniteField.pow_card a

/-- Characteristic-two specialization used by the positive-order squarefree consumer. -/
def inverseSquare [CharP E 2] (result : SearchResult E) (index : FiniteIndex E) :
    result.FieldType → result.FieldType :=
  result.inverseFrobenius 2 index

@[simp] theorem inverseSquare_sq [CharP E 2]
    (result : SearchResult E) (index : FiniteIndex E)
    (hcard : result.baseCardinality = index.cardinality) (a : result.FieldType) :
    result.inverseSquare index a ^ 2 = a := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact result.inverseFrobenius_pow 2 index hcard a

/-- The constructed quotient is itself a reusable finite-field input. This is
the recursion boundary used when a later positive-order stage needs a larger field. -/
def finiteIndex (result : SearchResult E) (index : FiniteIndex E)
    (hcard : result.baseCardinality = index.cardinality) : FiniteIndex result.FieldType where
  cardinality := index.cardinality ^ result.degree
  one_lt_cardinality := by
    apply Nat.one_lt_pow
    · have hdegree : result.modulus.toPoly.natDegree = result.degree := result.degree_eq
      exact (hdegree ▸ result.irreducible.natDegree_pos).ne'
    · exact index.one_lt_cardinality
  decode := result.coordinateIndex index hcard
  encode := (result.coordinateIndex index hcard).symm
  decode_encode := (result.coordinateIndex index hcard).apply_symm_apply
  encode_decode := (result.coordinateIndex index hcard).symm_apply_apply

instance {p : Nat} [CharP E p] (result : SearchResult E) : CharP result.FieldType p := by
  let _ : Fact result.modulus.monic := ⟨result.monic⟩
  let _ : Fact (Irreducible result.modulus.toPoly) := ⟨result.irreducible⟩
  infer_instance

@[simp] theorem characteristic {p : Nat} [CharP E p] (result : SearchResult E) :
    ringChar result.FieldType = p := ringChar.eq _ p

end SearchResult

/-- Observable result of extension dispatch. The base-capacity guard is evaluated
before polynomial enumeration, and the impossible search-failure branch remains explicit. -/
inductive ExtensionSearchResult (E : Type*) [Field E] [BEq E]
    (baseCardinality requested : Nat) where
  | base (capacity : requested ≤ baseCardinality)
  | extension (result : SearchResult E)
  | searchFailure (degree : Nat)

/-- Allocate the requested base-field prefix on the base-capacity branch. -/
def baseCenters {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (requested : Nat)
    (capacity : requested ≤ index.cardinality) : List E :=
  indexedPrefix index.equivFin requested capacity

@[simp] theorem baseCenters_length {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (requested : Nat)
    (capacity : requested ≤ index.cardinality) :
    (baseCenters index requested capacity).length = requested :=
  indexedPrefix_length _ _ _

theorem baseCenters_nodup {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (requested : Nat)
    (capacity : requested ≤ index.cardinality) :
    (baseCenters index requested capacity).Nodup :=
  indexedPrefix_nodup _ _ _

inductive ExtensionSearchBranch where
  | base | extension | searchFailure
  deriving DecidableEq, BEq, Repr

def ExtensionSearchResult.branch {E : Type*} [Field E] [BEq E]
    {baseCardinality requested : Nat} :
    ExtensionSearchResult E baseCardinality requested → ExtensionSearchBranch
  | .base _ => .base
  | .extension _ => .extension
  | .searchFailure _ => .searchFailure

/-- Search the complete monic list at the computed least positive degree. -/
def run {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (requested : Nat) :
    ExtensionSearchResult E index.cardinality requested :=
  if hbase : requested ≤ index.cardinality then .base hbase
  else
    let degree := leastDegree index.cardinality requested
    have hdegree := (leastDegree_spec (B := requested) index.one_lt_cardinality).1
    let p := firstIrreducible index degree hdegree
    have hp := firstIrreducible_sound index degree hdegree
    .extension {
      requested := requested
      baseCardinality := index.cardinality
      degree := degree
      modulus := p
      monic := hp.1
      irreducible := hp.2.2
      degree_eq := hp.2.1
      sufficient := (leastDegree_spec index.one_lt_cardinality).2.1
      least := (leastDegree_spec index.one_lt_cardinality).2.2 }

theorem run_base_iff {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (requested : Nat) :
    (run index requested).branch = .base ↔ requested ≤ index.cardinality := by
  by_cases hbase : requested ≤ index.cardinality
  · simp [run, hbase, ExtensionSearchResult.branch]
  · simp [run, hbase, ExtensionSearchResult.branch]

theorem run_extension_iff {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (requested : Nat) :
    (run index requested).branch = .extension ↔ index.cardinality < requested := by
  by_cases hbase : requested ≤ index.cardinality
  · simp [run, hbase, ExtensionSearchResult.branch]
  · have : index.cardinality < requested := by omega
    simp [run, hbase, ExtensionSearchResult.branch, this]

/-- Every extension payload returned by `run` records the original request,
the supplied base cardinality, and the computed least degree literally. -/
theorem run_extension_payload {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (requested : Nat) (result : SearchResult E)
    (h : run index requested = .extension result) :
    result.requested = requested ∧
      result.baseCardinality = index.cardinality ∧
      result.degree = leastDegree index.cardinality requested := by
  unfold run at h
  split at h
  · contradiction
  · cases h
    exact ⟨rfl, rfl, rfl⟩

/-- The proof-only finite-field existence theorem certifies that the explicit
failure constructor is unreachable. -/
theorem run_ne_searchFailure {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (requested degree : Nat) :
    run index requested ≠ .searchFailure degree := by
  by_cases hbase : requested ≤ index.cardinality
  · simp [run, hbase]
  · simp [run, hbase]

theorem run_searchFailure_ne {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (index : FiniteIndex E) (requested : Nat) :
    (run index requested).branch ≠ .searchFailure := by
  intro h
  generalize hrun : run index requested = result at h
  cases result with
  | base hbase => simp [ExtensionSearchResult.branch] at h
  | extension data => simp [ExtensionSearchResult.branch] at h
  | searchFailure degree => exact run_ne_searchFailure index requested degree hrun

end ArkLib.FiniteField.ExplicitConstruction
