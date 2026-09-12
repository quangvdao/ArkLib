/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.DenseMacaulay

/-!
# Combinatorial correctness of the dense Macaulay matrix

This file proves that the executable weak-composition basis enumerates each
critical-degree monomial exactly once, that every basis row is assigned to an
equation, and that the stored matrix entry is the coefficient prescribed by
Macaulay's first-dividing-power row rule.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.DenseMacaulay

open CPoly CPoly.CMvPolynomial

variable {F : Type*} [CommRing F] [BEq F] [LawfulBEq F]

/-- Adding a leading coordinate adds it to the total degree. -/
theorem totalDegree_insertIdx_zero {n head : ℕ} (tail : CMvMonomial n) :
    CMvMonomial.totalDegree (tail.insertIdx 0 head) = head + tail.totalDegree := by
  unfold CMvMonomial.totalDegree
  rw [← Vector.sum_toArray, Vector.toArray_insertIdx, Array.insertIdx_zero,
    Array.sum_append, Array.sum_singleton, Vector.sum_toArray]

/-- Every enumerated weak composition has the requested weight. -/
theorem mem_weakCompositions_totalDegree :
    ∀ {count degree : ℕ} {m : CMvMonomial count},
      m ∈ weakCompositions count degree → m.totalDegree = degree := by
  intro count
  induction count with
  | zero =>
      intro degree m hmem
      cases degree with
      | zero =>
          simp only [weakCompositions, List.mem_singleton] at hmem
          subst m
          rfl
      | succ degree => simp [weakCompositions] at hmem
  | succ count ih =>
      intro degree m hmem
      simp only [weakCompositions, List.mem_flatMap, List.mem_range,
        List.mem_map] at hmem
      obtain ⟨head, hhead, tail, htail, rfl⟩ := hmem
      rw [totalDegree_insertIdx_zero, ih htail]
      omega

/-- Removing and reinserting the leading coordinate recovers a monomial. -/
theorem insertIdx_zero_eraseIdx {n : ℕ} (m : CMvMonomial (n + 1)) :
    (m.eraseIdx 0).insertIdx 0 (m.get 0) = m := by
  apply CMvMonomial.ext
  intro i hi
  cases i with
  | zero =>
      exact Vector.getElem_insertIdx_self (xs := m.eraseIdx 0) (i := 0)
        (x := m.get 0) (by omega)
  | succ j =>
      rw [Vector.getElem_insertIdx_of_gt (xs := m.eraseIdx 0) (i := 0)
          (k := j + 1) (by omega) (by omega)]
      simp only [Nat.add_sub_cancel]
      exact Vector.getElem_eraseIdx_of_ge (xs := m) (i := 0) (j := j)
        (by omega) (by omega) (by omega)

/-- The first coordinate of a leading-coordinate insertion is the inserted
value. -/
theorem get_insertIdx_zero {n head : ℕ} (tail : CMvMonomial n) :
    (tail.insertIdx 0 head).get (0 : Fin (n + 1)) = head := by
  exact Vector.getElem_insertIdx_self (xs := tail) (i := 0) (x := head) (by omega)

/-- Total degree decomposes into the first coordinate and the remaining
coordinates. -/
theorem totalDegree_eq_head_add_tail {n : ℕ} (m : CMvMonomial (n + 1)) :
    m.totalDegree = m.get 0 + CMvMonomial.totalDegree (m.eraseIdx 0) := by
  let tail : CMvMonomial n := m.eraseIdx 0
  calc
    m.totalDegree = CMvMonomial.totalDegree (tail.insertIdx 0 (m.get 0)) := by
      rw [insertIdx_zero_eraseIdx]
    _ = _ := totalDegree_insertIdx_zero _

/-- Every monomial of the requested weight occurs in the executable weak
composition enumeration. -/
theorem mem_weakCompositions_of_totalDegree :
    ∀ {count degree : ℕ} {m : CMvMonomial count},
      m.totalDegree = degree → m ∈ weakCompositions count degree := by
  intro count
  induction count with
  | zero =>
      intro degree m hdegree
      have hm : m = (#v[] : CMvMonomial 0) := by
        apply CMvMonomial.ext
        intro i hi
        omega
      subst m
      simp only [CMvMonomial.totalDegree, Vector.sum_empty] at hdegree
      subst degree
      simp [weakCompositions]
  | succ count ih =>
      intro degree m hdegree
      let head := m.get (0 : Fin (count + 1))
      let tail : CMvMonomial count := m.eraseIdx 0
      have hdecomposition : m = tail.insertIdx 0 head := by
        simpa [head, tail] using (insertIdx_zero_eraseIdx m).symm
      have hhead : head ≤ degree := by
        rw [← hdegree, totalDegree_eq_head_add_tail]
        exact Nat.le_add_right _ _
      have htail : tail.totalDegree = degree - head := by
        rw [← Nat.add_left_cancel_iff]
        calc
          head + tail.totalDegree = m.totalDegree := by
            rw [totalDegree_eq_head_add_tail]
          _ = degree := hdegree
          _ = head + (degree - head) := (Nat.add_sub_of_le hhead).symm
      simp only [weakCompositions, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨head, by omega, tail, ih htail, hdecomposition.symm⟩

/-- Membership in `weakCompositions` is exactly the requested total degree. -/
theorem mem_weakCompositions_iff_totalDegree {count degree : ℕ}
    {m : CMvMonomial count} :
    m ∈ weakCompositions count degree ↔ m.totalDegree = degree :=
  ⟨mem_weakCompositions_totalDegree, mem_weakCompositions_of_totalDegree⟩

/-- The weak-composition enumeration contains no duplicate monomials. -/
theorem weakCompositions_nodup :
    ∀ count degree, (weakCompositions count degree).Nodup := by
  intro count
  induction count with
  | zero =>
      intro degree
      cases degree <;> simp [weakCompositions]
  | succ count ih =>
      intro degree
      rw [weakCompositions, List.nodup_flatMap]
      constructor
      · intro head _
        apply List.Nodup.map
        · intro left right hequal
          have := congrArg (fun m => m.eraseIdx 0) hequal
          simpa only [Vector.eraseIdx_insertIdx_self] using this
        · exact ih (degree - head)
      · refine List.Pairwise.imp ?_ (List.pairwise_lt_range)
        intro left right hlt
        dsimp only [Function.onFun]
        rw [List.disjoint_iff_ne]
        intro leftMonomial hleft rightMonomial hright hequal
        obtain ⟨leftTail, _, rfl⟩ := List.mem_map.mp hleft
        obtain ⟨rightTail, _, rfl⟩ := List.mem_map.mp hright
        have hheads := congrArg
          (fun m : CMvMonomial (count + 1) => m.get 0) hequal
        rw [get_insertIdx_zero leftTail, get_insertIdx_zero rightTail] at hheads
        omega

omit [BEq F] [LawfulBEq F] in
/-- The stored Macaulay basis contains exactly the critical-degree
monomials. -/
theorem mem_basis_iff_totalDegree {n : ℕ}
    (system : Fin n → CMvPolynomial n F) {m : CMvMonomial (n + 1)} :
    m ∈ basis system ↔ m.totalDegree = macaulayDegree system :=
  mem_weakCompositions_iff_totalDegree

omit [BEq F] [LawfulBEq F] in
/-- The stored Macaulay basis has no duplicate rows or columns. -/
theorem basis_nodup {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    (basis system).Nodup :=
  weakCompositions_nodup _ _

/-- Reading a tail coordinate after deleting the leading coordinate agrees
with the corresponding successor coordinate. -/
theorem get_eraseIdx_zero {n : ℕ} (m : CMvMonomial (n + 1)) (i : Fin n) :
    (m.eraseIdx 0).get i = m.get i.succ := by
  exact Vector.getElem_eraseIdx_of_ge (xs := m) (i := 0) (j := i.val)
    (by omega) (by omega) (by omega)

/-- Vector total degree is the finite sum of its coordinates. -/
theorem totalDegree_eq_sum_get :
    ∀ {n : ℕ} (m : CMvMonomial n), m.totalDegree = ∑ i, m.get i := by
  intro n
  induction n with
  | zero =>
      intro m
      have hm : m = (#v[] : CMvMonomial 0) := by
        apply CMvMonomial.ext
        intro i hi
        omega
      subst m
      simp [CMvMonomial.totalDegree]
  | succ n ih =>
      intro m
      rw [totalDegree_eq_head_add_tail, Fin.sum_univ_succ, ih]
      apply congrArg (m.get 0 + ·)
      apply Finset.sum_congr rfl
      intro i _
      exact get_eraseIdx_zero m i

/-- At Macaulay's critical degree, some paired leading power divides every
row monomial. -/
theorem exists_degree_le_of_totalDegree_eq_critical {count : ℕ}
    (degrees : Fin count → ℕ)
    (m : CMvMonomial count)
    (hdegree : m.totalDegree = 1 + ∑ i, (degrees i - 1)) :
    ∃ i, degrees i ≤ m.get i := by
  by_contra hnone
  rw [not_exists] at hnone
  have hsum : (∑ i, m.get i) ≤ ∑ i, (degrees i - 1) := by
    apply Finset.sum_le_sum
    intro i _
    have hlt : m.get i < degrees i := Nat.lt_of_not_ge (hnone i)
    omega
  rw [← totalDegree_eq_sum_get, hdegree] at hsum
  omega

omit [BEq F] [LawfulBEq F] in
/-- Every homogeneous equation degree is positive. -/
theorem equationDegree_pos {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (i : Fin (n + 1)) : 0 < equationDegree system i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [equationDegree]
  · simp [equationDegree, denseDegree_pos]

omit [BEq F] [LawfulBEq F] in
/-- The `none` fallback in `rowEquation?` is unreachable for a critical-degree
monomial. -/
theorem rowEquation?_ne_none_of_totalDegree {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (m : CMvMonomial (n + 1))
    (hdegree : m.totalDegree = macaulayDegree system) :
    rowEquation? (equationDegree system) m ≠ none := by
  have hexists : ∃ i, equationDegree system i ≤ m.get i := by
    apply exists_degree_le_of_totalDegree_eq_critical
    simpa [macaulayDegree] using hdegree
  rw [← Option.isSome_iff_ne_none]
  unfold rowEquation?
  rw [List.find?_isSome]
  obtain ⟨i, hi⟩ := hexists
  exact ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, by simpa using hi⟩

omit [BEq F] [LawfulBEq F] in
/-- In particular, the fallback is unreachable for every stored matrix row. -/
theorem rowEquation?_basis_ne_none {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (i : Fin (basis system).length) :
    rowEquation? (equationDegree system) (basis system)[i] ≠ none := by
  apply rowEquation?_ne_none_of_totalDegree system
  exact mem_weakCompositions_totalDegree (List.getElem_mem i.isLt)

/-- A returned row equation has its paired leading power dividing the row
monomial. -/
theorem rowEquation?_eq_some_degree_le {count : ℕ}
    (degrees : Fin count → ℕ) (m : CMvMonomial count) (i : Fin count)
    (hequation : rowEquation? degrees m = some i) :
    degrees i ≤ m.get i := by
  unfold rowEquation? at hequation
  have htest : decide (degrees i ≤ m.get i) = true :=
    List.find?_some (p := fun j => decide (degrees j ≤ m.get j)) hequation
  exact of_decide_eq_true htest

/-- The selected equation is the least index whose paired leading power
divides the row monomial. -/
theorem rowEquation?_eq_some_least {count : ℕ}
    (degrees : Fin count → ℕ) (m : CMvMonomial count) (i : Fin count)
    (hequation : rowEquation? degrees m = some i) :
    ∀ j, j < i → m.get j < degrees j := by
  unfold rowEquation? at hequation
  obtain ⟨_, k, hk, hget, hprior⟩ :=
    List.find?_eq_some_iff_getElem.mp hequation
  have hkCount : k < count := by simpa using hk
  have hkEq : k = i.val := by
    have hstored := List.getElem_ofFn
      (f := fun j : Fin count => j) hk
    have hfin : (⟨k, hkCount⟩ : Fin count) = i := hstored.symm.trans hget
    exact congrArg Fin.val hfin
  intro j hj
  have hjk : j.val < k := by omega
  have hfalse := hprior j.val hjk
  have hjLength : j.val < (List.ofFn fun j : Fin count => j).length := by
    simp
  rw [List.getElem_ofFn hjLength] at hfalse
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hfalse
  apply Nat.lt_of_not_ge
  simpa only [Fin.eta] using hfalse

/-- Canonical equation assigned to a basis row, using the proof that the
critical-degree search cannot fail. -/
def basisRowEquation {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (i : Fin (basis system).length) : Fin (n + 1) :=
  (rowEquation? (equationDegree system) (basis system)[i]).get <|
    Option.isSome_iff_ne_none.mpr (rowEquation?_basis_ne_none system i)

omit [BEq F] [LawfulBEq F] in
/-- The canonical row equation is exactly the result of the executable
first-dividing-power search. -/
theorem rowEquation?_basis_eq_some {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (i : Fin (basis system).length) :
    rowEquation? (equationDegree system) (basis system)[i] =
      some (basisRowEquation system i) := by
  exact Option.eq_some_of_isSome _

/-- Exact coefficient specification for every stored matrix entry once its row
equation is named. -/
theorem matrix_apply_of_rowEquation?_eq_some {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (i j : Fin (basis system).length)
    (equation : Fin (n + 1))
    (hequation : rowEquation? (equationDegree system) (basis system)[i] =
      some equation) :
    matrix system i j =
      rowEntry (rowMultiplier (equationDegree system equation) equation
        (basis system)[i]) (basis system)[j]
        (homogeneousTerms system equation) := by
  change (match rowEquation? (equationDegree system) (basis system)[i] with
    | none => 0
    | some equation =>
        rowEntry (rowMultiplier (equationDegree system equation) equation
          (basis system)[i]) (basis system)[j]
          (homogeneousTerms system equation)) = _
  rw [hequation]

/-- Unconditional fill specification using the canonical equation assigned
to a stored row. -/
theorem matrix_apply {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (i j : Fin (basis system).length) :
    matrix system i j =
      rowEntry (rowMultiplier
        (equationDegree system (basisRowEquation system i))
        (basisRowEquation system i) (basis system)[i])
        (basis system)[j]
        (homogeneousTerms system (basisRowEquation system i)) := by
  apply matrix_apply_of_rowEquation?_eq_some
  exact rowEquation?_basis_eq_some system i

/-- Mapping a computable monomial into the semantic polynomial ring does not
increase its total degree. -/
theorem totalDegree_monomial_le {k : ℕ} (m : CMvMonomial k) (c : F) :
    (fromCMvPolynomial (CMvPolynomial.monomial m c)).totalDegree ≤
      m.totalDegree := by
  rw [CMvPolynomial.fromCMvPolynomial_monomial]
  calc
    _ ≤ Finsupp.sum m.toFinsupp (fun _ exponent => exponent) :=
      MvPolynomial.totalDegree_monomial_le _ _
    _ = m.totalDegree := by
      rw [totalDegree_eq_sum_get, Finsupp.sum_fintype]
      · rfl
      · intro i
        simp

/-- An auxiliary coefficient is linear in the parameter variables. -/
theorem auxiliaryCoefficient_totalDegree_le_one {n : ℕ} (i : Fin (n + 1)) :
    (fromCMvPolynomial (auxiliaryCoefficient (F := F) i)).totalDegree ≤ 1 := by
  unfold auxiliaryCoefficient
  exact (totalDegree_monomial_le _ _).trans_eq (by
    rw [totalDegree_eq_sum_get]
    calc
      (∑ j, (auxiliaryParameterMonomial i).get j) =
          ∑ j, if j = Fin.castSucc i then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        simp [auxiliaryParameterMonomial, Fin.ext_iff]
      _ = 1 := by simp)

/-- The perturbation coefficient `-s` is linear in the parameter variables. -/
theorem negativeS_totalDegree_le_one {n : ℕ} :
    (fromCMvPolynomial (negativeS (F := F) (n := n))).totalDegree ≤ 1 := by
  unfold negativeS
  exact (totalDegree_monomial_le _ _).trans_eq (by
    rw [totalDegree_eq_sum_get]
    calc
      (∑ j, (sParameterMonomial (n := n)).get j) =
          ∑ j, if j = Fin.last (n + 1) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        simp [sParameterMonomial, Fin.ext_iff]
      _ = 1 := by simp)

private theorem rowEntry_foldl_totalDegree_le_one {n : ℕ}
    (multiplier column : CMvMonomial (n + 1))
    (terms : HomogeneousTerms n F) (accumulator : Parameters n F)
    (haccumulator : (fromCMvPolynomial accumulator).totalDegree ≤ 1)
    (hterms : ∀ term ∈ terms,
      (fromCMvPolynomial term.2).totalDegree ≤ 1) :
    (fromCMvPolynomial (terms.foldl
      (fun result term =>
        if multiplier + term.1 = column then result + term.2 else result)
      accumulator)).totalDegree ≤ 1 := by
  induction terms generalizing accumulator with
  | nil => exact haccumulator
  | cons term terms ih =>
      simp only [List.foldl_cons]
      apply ih
      · split
        · rw [CMvPolynomial.fromCMvPolynomial_add']
          exact (MvPolynomial.totalDegree_add _ _).trans
            (max_le haccumulator (hterms term (by simp)))
        · exact haccumulator
      · intro remaining hremaining
        exact hterms remaining (by simp [hremaining])

/-- A row coefficient remains linear when equal-column contributions are
accumulated. -/
theorem rowEntry_totalDegree_le_one {n : ℕ}
    (multiplier column : CMvMonomial (n + 1))
    (terms : HomogeneousTerms n F)
    (hterms : ∀ term ∈ terms,
      (fromCMvPolynomial term.2).totalDegree ≤ 1) :
    (fromCMvPolynomial (rowEntry multiplier column terms)).totalDegree ≤ 1 := by
  unfold rowEntry
  apply rowEntry_foldl_totalDegree_le_one
  · simp
  · exact hterms

/-- Every coefficient occurring in a stored homogeneous equation is constant
or linear in `(u₀,...,uₙ,s)`. -/
theorem homogeneousTerms_coefficient_totalDegree_le_one {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (equation : Fin (n + 1))
    (term : CMvMonomial (n + 1) × Parameters n F)
    (hterm : term ∈ homogeneousTerms system equation) :
    (fromCMvPolynomial term.2).totalDegree ≤ 1 := by
  cases equation using Fin.cases with
  | zero =>
      simp only [homogeneousTerms, Fin.cases_zero] at hterm
      unfold auxiliaryTerms at hterm
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hterm
      exact auxiliaryCoefficient_totalDegree_le_one i
  | succ i =>
      simp only [homogeneousTerms, Fin.cases_succ] at hterm
      unfold perturbedTerms at hterm
      rw [List.mem_append] at hterm
      rcases hterm with hsource | hperturbation
      · obtain ⟨sourceTerm, _, rfl⟩ := List.mem_map.mp hsource
        rw [CMvPolynomial.fromCMvPolynomial_C, MvPolynomial.totalDegree_C]
        omega
      · simp only [List.mem_singleton] at hperturbation
        subst term
        exact negativeS_totalDegree_le_one

/-- Every entry of the dense Macaulay matrix is constant or linear in the
parameter variables. -/
theorem matrix_entry_totalDegree_le_one {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (i j : Fin (basis system).length) :
    (fromCMvPolynomial (matrix system i j)).totalDegree ≤ 1 := by
  change (fromCMvPolynomial
    (match rowEquation? (equationDegree system) (basis system)[i] with
    | none => 0
    | some equation =>
        rowEntry (rowMultiplier (equationDegree system equation) equation
          (basis system)[i]) (basis system)[j]
          (homogeneousTerms system equation))).totalDegree ≤ 1
  split
  · simp
  · apply rowEntry_totalDegree_le_one
    exact homogeneousTerms_coefficient_totalDegree_le_one system _

omit [BEq F] [LawfulBEq F] in
/-- A determinant of parameter polynomials of degree at most `degree` has
total degree at most the matrix dimension times `degree`. -/
theorem totalDegree_det_le_card {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ F)) (degree : ℕ)
    (hentry : ∀ i j, (M i j).totalDegree ≤ degree) :
    M.det.totalDegree ≤ Fintype.card ι * degree := by
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro permutation _
  refine (MvPolynomial.totalDegree_smul_le
    (permutation.sign : ℤ) (∏ i, M (permutation i) i)).trans ?_
  refine (MvPolynomial.totalDegree_finsetProd Finset.univ
    (fun i => M (permutation i) i)).trans ?_
  calc
    (∑ i, (M (permutation i) i).totalDegree) ≤ ∑ _i : ι, degree := by
      apply Finset.sum_le_sum
      intro i _
      exact hentry _ _
    _ = Fintype.card ι * degree := by simp

/-- The generalized characteristic determinant has total parameter degree at
most its matrix size. -/
theorem characteristic_totalDegree_le_matrixSize {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    (characteristic system).totalDegree ≤ (basis system).length := by
  rw [CPoly.totalDegree_equiv (S := F)]
  unfold characteristic
  change ((CPoly.polyRingEquiv (n := n + 2) (R := F))
    ((matrix system).det)).totalDegree ≤ _
  rw [RingEquiv.map_det (CPoly.polyRingEquiv (n := n + 2) (R := F))
    (matrix system)]
  simpa using totalDegree_det_le_card
    ((CPoly.polyRingEquiv (n := n + 2) (R := F)).mapMatrix
      (matrix system)) 1
    (fun i j => by
      change (fromCMvPolynomial (matrix system i j)).totalDegree ≤ 1
      exact matrix_entry_totalDegree_le_one system i j)

/-- Each individual parameter degree of the characteristic is bounded by the
matrix size. -/
theorem characteristic_parameterDegree_le_matrixSize {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (i : Fin (n + 2)) :
    (fromCMvPolynomial (characteristic system)).degreeOf i ≤
      (basis system).length :=
  (MvPolynomial.degreeOf_le_totalDegree _ _).trans <| by
    simpa [CPoly.totalDegree_equiv (S := F)] using
      characteristic_totalDegree_le_matrixSize system

end ArkLib.Rojas.Producer.DenseMacaulay
