/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.DenseMacaulay
public import CompPoly.ToMathlib.Finsupp.Fin

/-!
# Semantics of the lowest perturbation exponent

This file proves that the executable `DenseMacaulay.lowestSExponent?` scanner
finds exactly the first nonzero coefficient in the final parameter `s`.
The proof works directly with the canonical sparse term map used by CompPoly.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.DenseMacaulay

open CPoly CPoly.CMvPolynomial

variable {F : Type*} [CommRing F] [BEq F] [LawfulBEq F]

@[simp]
theorem toFinsupp_dropS {n : ℕ} (monomial : CMvMonomial (n + 2)) :
    (dropS monomial).toFinsupp = monomial.toFinsupp.init := by
  ext i
  rw [Finsupp.init_apply]
  unfold dropS CMvMonomial.toFinsupp
  change
    (Vector.ofFn fun j : Fin (n + 1) => monomial.get ⟨j.val, by omega⟩).get i =
      monomial.get i.castSucc
  rw [Vector.get_ofFn]
  apply congrArg (fun j => monomial.get j)
  apply Fin.ext
  rfl

/-- Executable extraction of the coefficient of `s ^ degree`, expressed as a
semantic multivariate sum over the input polynomial. -/
theorem fromCMvPolynomial_coefficientInS {n : ℕ} (degree : ℕ) (H : Parameters n F) :
    fromCMvPolynomial (coefficientInS degree H) =
      Finsupp.sum (AddMonoidAlgebra.coeff (fromCMvPolynomial H))
        (fun monomial coefficient =>
          if monomial (Fin.last (n + 1)) = degree then
            MvPolynomial.monomial monomial.init coefficient
          else 0) := by
  let selected : CMvMonomial (n + 2) → F → CMvPolynomial (n + 1) F :=
    fun monomial coefficient =>
      if sExponent monomial = degree then
        CMvPolynomial.monomial (dropS monomial) coefficient
      else 0
  have hfold : coefficientInS degree H =
      Finsupp.sum (AddMonoidAlgebra.coeff (fromCMvPolynomial H))
        (fun monomial coefficient =>
          if monomial (Fin.last (n + 1)) = degree then
            CMvPolynomial.monomial
              (dropS (CMvMonomial.ofFinsupp monomial)) coefficient
          else 0) := by
    calc
      coefficientInS degree H = H.val.toList.foldl
          (fun result term => selected term.1 term.2 + result) 0 := by
        unfold coefficientInS
        congr 1
        funext result term
        simp only [selected]
        split <;> simp_all
      _ = H.val.foldl (fun result monomial coefficient =>
          selected monomial coefficient + result) 0 := by
        rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
      _ = Finsupp.sum (AddMonoidAlgebra.coeff (fromCMvPolynomial H))
          (selected ∘ CMvMonomial.ofFinsupp) := CPoly.foldl_eq_sum
      _ = _ := by
        congr 1
        funext monomial coefficient
        simp only [Function.comp_apply, selected]
        congr 1
        simp only [sExponent, CMvMonomial.ofFinsupp]
        rw [Vector.get_ofFn]
        congr
  rw [hfold, fromCMvPolynomial_finsupp_sum]
  simp only [apply_ite, fromCMvPolynomial_monomial, toFinsupp_dropS,
    CMvMonomial.toFinsupp_ofFinsupp, CPoly.map_zero]

/-- Coefficient lookup after executable extraction is lookup in the original
polynomial with the requested final exponent appended. -/
theorem coeff_fromCMvPolynomial_coefficientInS {n : ℕ} (degree : ℕ)
    (H : Parameters n F) (monomial : Fin (n + 1) →₀ ℕ) :
    MvPolynomial.coeff monomial (fromCMvPolynomial (coefficientInS degree H)) =
      MvPolynomial.coeff (monomial.snoc degree) (fromCMvPolynomial H) := by
  rw [fromCMvPolynomial_coefficientInS, Finsupp.sum]
  let q := fromCMvPolynomial H
  change MvPolynomial.coeff monomial
      (∑ source ∈ q.support, if source (Fin.last (n + 1)) = degree then
        MvPolynomial.monomial source.init (q.coeff source) else 0) =
    q.coeff (monomial.snoc degree)
  rw [MvPolynomial.coeff_sum]
  by_cases hmem : monomial.snoc degree ∈ q.support
  · rw [Finset.sum_eq_single (monomial.snoc degree)]
    · simp
    · intro source hsource hne
      by_cases hlast : source (Fin.last (n + 1)) = degree
      · rw [if_pos hlast, MvPolynomial.coeff_monomial, if_neg]
        intro hinit
        apply hne
        rw [← Finsupp.snoc_init_self source, hlast, hinit]
      · simp [hlast]
    · intro hnot
      exact (hnot hmem).elim
  · rw [Finset.sum_eq_zero]
    · exact (MvPolynomial.notMem_support_iff.mp hmem).symm
    · intro source hsource
      by_cases hlast : source (Fin.last (n + 1)) = degree
      · rw [if_pos hlast, MvPolynomial.coeff_monomial, if_neg]
        intro hinit
        apply hmem
        have heq : source = monomial.snoc degree := by
          rw [← Finsupp.snoc_init_self source, hlast, hinit]
        simpa only [← heq] using hsource
      · simp [hlast]

omit [BEq F] [LawfulBEq F] in
private theorem mem_support_fromCMvPolynomial_iff {n : ℕ} (H : Parameters n F)
    (monomial : CMvMonomial (n + 2)) :
    monomial.toFinsupp ∈ (fromCMvPolynomial H).support ↔ monomial ∈ H.monomials := by
  simp only [MvPolynomial.mem_support_iff, CPoly.coeff_eq,
    CMvMonomial.ofFinsupp_toFinsupp, CPoly.Lawful.mem_monomials_iff]
  unfold CMvPolynomial.coeff
  rw [CPoly.Lawful.mem_iff]
  constructor
  · intro h
    by_cases hm : H.val[monomial]? = none
    · simp [hm] at h
    · obtain ⟨coefficient, hcoefficient⟩ := Option.ne_none_iff_exists'.mp hm
      refine ⟨coefficient, ?_, hcoefficient⟩
      simpa [hcoefficient] using h
  · rintro ⟨coefficient, hcoefficient, hlookup⟩
    rw [← CPoly.Lawful.getElem?_eq_val_getElem?, hlookup]
    simpa

/-- A coefficient in `s` is nonzero exactly when the stored polynomial has a
monomial with that final exponent. -/
theorem coefficientInS_ne_zero_iff {n : ℕ} (degree : ℕ) (H : Parameters n F) :
    coefficientInS degree H ≠ 0 ↔
      ∃ monomial ∈ H.monomials, sExponent monomial = degree := by
  let q := fromCMvPolynomial H
  have hsemantic : coefficientInS degree H ≠ 0 ↔
      ∃ source ∈ q.support, source (Fin.last (n + 1)) = degree := by
    constructor
    · intro hout
      have hfrom : fromCMvPolynomial (coefficientInS degree H) ≠ 0 := by
        intro hzero
        apply hout
        apply fromCMvPolynomial_injective
        simpa using hzero
      obtain ⟨target, htarget⟩ := MvPolynomial.support_nonempty.mpr hfrom
      refine ⟨target.snoc degree, ?_, by simp⟩
      rw [MvPolynomial.mem_support_iff]
      rw [← coeff_fromCMvPolynomial_coefficientInS degree H target]
      exact MvPolynomial.mem_support_iff.mp htarget
    · rintro ⟨source, hsource, hdegree⟩ hzero
      have hcoefficient := coeff_fromCMvPolynomial_coefficientInS degree H source.init
      rw [hzero, CPoly.map_zero, MvPolynomial.coeff_zero] at hcoefficient
      have hreconstruct : source.init.snoc degree = source := by
        calc
          source.init.snoc degree = source.init.snoc (source (Fin.last (n + 1))) :=
            congrArg source.init.snoc hdegree.symm
          _ = source := Finsupp.snoc_init_self source
      have hsourceZero : q.coeff source = 0 := by
        rw [← hreconstruct]
        exact hcoefficient.symm
      exact (MvPolynomial.mem_support_iff.mp hsource) hsourceZero
  rw [hsemantic]
  constructor
  · rintro ⟨source, hsource, hdegree⟩
    refine ⟨CMvMonomial.ofFinsupp source, ?_, ?_⟩
    · apply (mem_support_fromCMvPolynomial_iff H _).1
      simpa using hsource
    · unfold sExponent
      rw [CMvMonomial.ofFinsupp, Vector.get_ofFn]
      have hlast : (⟨n + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := Fin.ext rfl
      rw [hlast]
      exact hdegree
  · rintro ⟨monomial, hmonomial, hdegree⟩
    refine ⟨monomial.toFinsupp, ?_, ?_⟩
    · exact (mem_support_fromCMvPolynomial_iff H monomial).2 hmonomial
    · unfold sExponent at hdegree
      change monomial.get (Fin.last (n + 1)) = degree
      have hlast : (Fin.last (n + 1) : Fin (n + 2)) =
          ⟨n + 1, by omega⟩ := Fin.ext rfl
      rw [hlast]
      exact hdegree

/-- `lowestSExponent?` returns `degree` exactly when its coefficient is
nonzero and every lower coefficient vanishes. -/
theorem lowestSExponent?_eq_some_iff {n : ℕ} {degree : ℕ} {H : Parameters n F} :
    lowestSExponent? H = some degree ↔
      coefficientInS degree H ≠ 0 ∧
        ∀ lower < degree, coefficientInS lower H = 0 := by
  rw [lowestSExponent?, List.min?_eq_some_iff]
  constructor
  · rintro ⟨hdegree, hleast⟩
    obtain ⟨monomial, hmonomial, hs⟩ := List.mem_map.mp hdegree
    refine ⟨(coefficientInS_ne_zero_iff degree H).2
      ⟨monomial, hmonomial, hs⟩, ?_⟩
    intro lower hlower
    by_contra hnonzero
    obtain ⟨lowerMonomial, hlowerMonomial, hsLower⟩ :=
      (coefficientInS_ne_zero_iff lower H).1 hnonzero
    have hmem : lower ∈ H.monomials.map sExponent :=
      List.mem_map.mpr ⟨lowerMonomial, hlowerMonomial, hsLower⟩
    exact (Nat.not_le_of_gt hlower) (hleast lower hmem)
  · rintro ⟨hnonzero, hlower⟩
    obtain ⟨monomial, hmonomial, hs⟩ :=
      (coefficientInS_ne_zero_iff degree H).1 hnonzero
    refine ⟨List.mem_map.mpr ⟨monomial, hmonomial, hs⟩, ?_⟩
    intro exponent hexponent
    by_contra hnotle
    have hlt : exponent < degree := Nat.lt_of_not_ge hnotle
    have hzero := hlower exponent hlt
    obtain ⟨lowerMonomial, hlowerMonomial, hsLower⟩ := List.mem_map.mp hexponent
    exact (coefficientInS_ne_zero_iff exponent H).2
      ⟨lowerMonomial, hlowerMonomial, hsLower⟩ hzero

private theorem monomials_eq_nil_iff {n : ℕ} (H : Parameters n F) :
    H.monomials = [] ↔ H = 0 := by
  constructor
  · intro hempty
    apply fromCMvPolynomial_injective
    rw [CPoly.map_zero, ← MvPolynomial.support_eq_empty]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨source, hsource⟩
    have hmonomial : CMvMonomial.ofFinsupp source ∈ H.monomials :=
      (mem_support_fromCMvPolynomial_iff H _).1 (by simpa using hsource)
    rw [hempty] at hmonomial
    simp at hmonomial
  · rintro rfl
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro monomial hmonomial
    exact CPoly.Lawful.not_mem_zero
      ((CPoly.Lawful.mem_monomials_iff).1 hmonomial)

/-- The lowest-exponent scan fails exactly for the zero parameter
polynomial. -/
theorem lowestSExponent?_eq_none_iff {n : ℕ} (H : Parameters n F) :
    lowestSExponent? H = none ↔ H = 0 := by
  rw [lowestSExponent?, List.min?_eq_none_iff, List.map_eq_nil_iff,
    monomials_eq_nil_iff]

end ArkLib.Rojas.Producer.DenseMacaulay
