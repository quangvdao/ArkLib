/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayIdentityCorrectness
public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayPerturbationCorrectness

/-!
# Input-only cases of total Macaulay division

Univariate systems of arbitrary degree and affine-linear square systems have no non-reduced
critical-degree monomials. Their extraneous determinant is one, so checked division always
returns the full characteristic determinant. These statements include constant and zero inputs.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.MacaulayQuotient

open CPoly CPoly.CMvPolynomial DenseMacaulay

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

private theorem countP_le_sum_map {α : Type*} (l : List α) (p : α → Bool) (a : α → ℕ)
    (h : ∀ i ∈ l, (if p i then 1 else 0) ≤ a i) :
    l.countP p ≤ (l.map a).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi := h i (by simp)
    have ht := ih (fun j hj ↦ h j (by simp [hj]))
    simp only [List.countP_cons, List.map_cons, List.sum_cons]
    split <;> simp_all <;> omega

omit [BEq F] [LawfulBEq F] in
/-- Each dividing positive power consumes at least one unit of total degree. -/
theorem count_dividingPowers_le_totalDegree {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (m : CMvMonomial (n + 1)) :
    (List.ofFn fun i : Fin (n + 1) ↦ i).countP
      (fun i ↦ decide (equationDegree system i ≤ m.get i)) ≤ m.totalDegree := by
  have h := countP_le_sum_map (List.ofFn fun i : Fin (n + 1) ↦ i)
    (fun i ↦ decide (equationDegree system i ≤ m.get i)) (fun i ↦ m.get i) (by
      intro i _
      split_ifs with hi
      · have hi' : equationDegree system i ≤ m.get i := of_decide_eq_true hi
        have hp := equationDegree_pos system i
        omega
      · omega)
  simpa [List.map_ofFn, List.sum_ofFn, totalDegree_eq_sum_get, Fin.sum_univ_succ] using h

omit [BEq F] [LawfulBEq F] in
/-- A degree-at-most-one monomial cannot belong to the extraneous minor. -/
theorem nonReducedB_eq_false_of_totalDegree_le_one {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (m : CMvMonomial (n + 1))
    (hm : m.totalDegree ≤ 1) : nonReducedB system m = false := by
  have h := count_dividingPowers_le_totalDegree system m
  simp only [nonReducedB, decide_eq_false_iff_not]
  omega

omit [BEq F] [LawfulBEq F] in
/-- Input equations of total degree at most one give critical degree one. -/
theorem macaulayDegree_eq_one_of_totalDegree_le_one {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (hlinear : ∀ i, (system i).totalDegree ≤ 1) :
    macaulayDegree system = 1 := by
  have hdegrees : ∀ i, equationDegree system i = 1 := by
    intro i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact max_eq_left (hlinear i)
  simp [macaulayDegree, hdegrees]

omit [BEq F] [LawfulBEq F] in
/-- Affine-linear input systems have an empty extraneous principal minor. -/
theorem extraneousIndices_eq_nil_of_totalDegree_le_one {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (hlinear : ∀ i, (system i).totalDegree ≤ 1) :
    extraneousIndices system = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro i _
  suffices h : nonReducedB system (basis system)[i] = false by
    intro ht
    cases h.symm.trans ht
  apply nonReducedB_eq_false_of_totalDegree_le_one
  have hmem : (basis system)[i] ∈ basis system := List.getElem_mem i.isLt
  have hdegree := (mem_basis_iff_totalDegree system).mp hmem
  rw [macaulayDegree_eq_one_of_totalDegree_le_one system hlinear] at hdegree
  exact hdegree.le

/-- Every affine-linear square input has a unit extraneous factor. -/
theorem extraneousFactor_eq_one_of_totalDegree_le_one {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (hlinear : ∀ i, (system i).totalDegree ≤ 1) :
    extraneousFactor system = 1 :=
  extraneousFactor_eq_one_of_extraneousIndices_eq_nil system
    (extraneousIndices_eq_nil_of_totalDegree_le_one system hlinear)

/-- Checked division is total on every affine-linear square input, including degenerate ones. -/
theorem macaulayQuotient?_eq_some_characteristic_of_totalDegree_le_one
    [DecidableEq F] {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (hlinear : ∀ i, (system i).totalDegree ≤ 1) :
    macaulayQuotient? system = some (characteristic system) :=
  macaulayQuotient?_eq_some_characteristic_of_extraneousIndices_eq_nil system
    (extraneousIndices_eq_nil_of_totalDegree_le_one system hlinear)

omit [BEq F] [LawfulBEq F] in
/-- In one affine variable, the critical homogeneous degree is the input degree envelope. -/
theorem macaulayDegree_univariate (system : Fin 1 → CMvPolynomial 1 F) :
    macaulayDegree system = denseDegree (system 0) := by
  have hp : 1 ≤ denseDegree (system 0) := le_max_left _ _
  simp [macaulayDegree, Fin.sum_univ_succ, equationDegree]
  omega

omit [BEq F] [LawfulBEq F] in
/-- Two dividing powers in two variables would exceed the Macaulay degree. -/
theorem nonReducedB_eq_false_univariate (system : Fin 1 → CMvPolynomial 1 F)
    (m : CMvMonomial 2) (hm : m.totalDegree = macaulayDegree system) :
    nonReducedB system m = false := by
  have hsum : m.get 0 + m.get 1 = denseDegree (system 0) := by
    simpa [totalDegree_eq_sum_get, Fin.sum_univ_two, macaulayDegree_univariate] using hm
  simp only [nonReducedB, List.ofFn_succ, List.ofFn_zero, List.countP_cons,
    List.countP_nil, equationDegree, Fin.cases_zero, Fin.cases_succ]
  by_cases h0 : 1 ≤ m.get 0
  · by_cases h1 : denseDegree (system 0) ≤ m.get 1
    · omega
    · norm_num [h0, h1]
  · by_cases h1 : denseDegree (system 0) ≤ m.get 1 <;> norm_num [h0, h1]

omit [BEq F] [LawfulBEq F] in
/-- Univariate inputs have an empty extraneous minor, independently of degree or coefficients. -/
theorem extraneousIndices_eq_nil_univariate (system : Fin 1 → CMvPolynomial 1 F) :
    extraneousIndices system = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro i _
  suffices h : nonReducedB system (basis system)[i] = false by
    intro ht
    cases h.symm.trans ht
  apply nonReducedB_eq_false_univariate
  exact (mem_basis_iff_totalDegree system).mp (List.getElem_mem i.isLt)

/-- Every univariate input has extraneous determinant one. -/
theorem extraneousFactor_eq_one_univariate (system : Fin 1 → CMvPolynomial 1 F) :
    extraneousFactor system = 1 :=
  extraneousFactor_eq_one_of_extraneousIndices_eq_nil system
    (extraneousIndices_eq_nil_univariate system)

/-- The actual checked quotient succeeds on all univariate inputs. -/
theorem macaulayQuotient?_eq_some_characteristic_univariate [DecidableEq F]
    (system : Fin 1 → CMvPolynomial 1 F) :
    macaulayQuotient? system = some (characteristic system) :=
  macaulayQuotient?_eq_some_characteristic_of_extraneousIndices_eq_nil system
    (extraneousIndices_eq_nil_univariate system)

/-- A checked quotient equal to the nonzero characteristic determinant gives
an actual successful perturbation output. -/
theorem exists_macaulayPerturbation_run_eq_ok_of_quotient_eq_characteristic
    [DecidableEq F] {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (hquotient : macaulayQuotient? system = some (characteristic system)) :
    ∃ output, MacaulayPerturbation.run system = .ok output := by
  have hcharacteristic : characteristic system ≠ 0 := characteristic_ne_zero system
  cases hexponent : lowestSExponent? (characteristic system) with
  | none =>
      exact False.elim <| hcharacteristic <|
        (lowestSExponent?_eq_none_iff (characteristic system)).mp hexponent
  | some exponent =>
      refine ⟨{
        quotient := characteristic system
        exponent := exponent
        perturbation := coefficientInS exponent (characteristic system) }, ?_⟩
      simp [MacaulayPerturbation.run, MacaulayPerturbation.fromCheckedQuotient?,
        hquotient, hexponent]

/-- The executable Macaulay perturbation producer succeeds on every
affine-linear square input, including degenerate systems. -/
theorem exists_macaulayPerturbation_run_eq_ok_of_totalDegree_le_one
    [DecidableEq F] {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (hlinear : ∀ i, (system i).totalDegree ≤ 1) :
    ∃ output, MacaulayPerturbation.run system = .ok output :=
  exists_macaulayPerturbation_run_eq_ok_of_quotient_eq_characteristic system
    (macaulayQuotient?_eq_some_characteristic_of_totalDegree_le_one system hlinear)

/-- The executable Macaulay perturbation producer succeeds on every
univariate input, independently of degree and coefficients. -/
theorem exists_macaulayPerturbation_run_eq_ok_univariate [DecidableEq F]
    (system : Fin 1 → CMvPolynomial 1 F) :
    ∃ output, MacaulayPerturbation.run system = .ok output :=
  exists_macaulayPerturbation_run_eq_ok_of_quotient_eq_characteristic system
    (macaulayQuotient?_eq_some_characteristic_univariate system)

end ArkLib.Rojas.Producer.MacaulayQuotient
