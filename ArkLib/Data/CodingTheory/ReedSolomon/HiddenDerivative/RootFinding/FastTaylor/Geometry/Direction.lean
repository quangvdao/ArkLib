/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.NonvanishingGrid
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Geometry.Matrix
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import CompPoly.Multivariate.Restrict

/-!
# Computed directions for a regular Taylor projection

Search the supplied scalar grid for nonvanishing of a certified positive-degree homogeneous
part, then compute a coordinate pivot and both inverse matrices. No direction or matrix is
accepted as an input certificate.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.Geometry.Direction

open CPoly CPoly.CMvPolynomial

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E] {r : ℕ}

/-- Keep exactly the homogeneous monomials of the requested total degree. -/
def homogeneousPart (b : ℕ) (p : CMvPolynomial (r + 1) E) : CMvPolynomial (r + 1) E :=
  restrictBy (fun m => m.totalDegree = b) p

/-- The executed monomial filter is the semantic homogeneous component. -/
theorem homogeneousPart_semantics (b : ℕ) (p : CMvPolynomial (r + 1) E) :
    fromCMvPolynomial (homogeneousPart b p) =
      MvPolynomial.homogeneousComponent b (fromCMvPolynomial p) := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_homogeneousComponent]
  change (homogeneousPart b p).coeff (CMvMonomial.ofFinsupp m) = _
  rw [homogeneousPart, coeff_restrictBy]
  have hd : (CMvMonomial.ofFinsupp m).totalDegree = m.degree := by
    change (Array.ofFn fun i => m i).sum = m.degree
    rw [Finsupp.degree_eq_sum, ← Array.sum_toList, Array.toList_ofFn, List.sum_ofFn]
  rw [hd]
  rfl

/-- Search for the direction, then construct its explicit forward and inverse coordinate maps. -/
def choose? (top : CMvPolynomial (r + 1) E) (values : List E) :
    Option ((Fin (r + 1) → E) × Matrix (Fin (r + 1)) (Fin (r + 1)) E ×
      Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
  (NonvanishingGrid.selectNonzero top values).bind fun v =>
    (ProjectionMatrix.construct? v).map fun matrices => (v, matrices)

/-- Every returned matrix pair is invertible and has the selected nonvanishing direction last. -/
theorem choose?_sound (top : CMvPolynomial (r + 1) E) (values : List E)
    (v : Fin (r + 1) → E) (M I : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (h : choose? top values = some (v, M, I)) :
    (∀ i, v i ∈ values) ∧ top.eval v ≠ 0 ∧ M * I = 1 ∧ I * M = 1 ∧
      ∀ i, M i (Fin.last r) = v i := by
  obtain ⟨u, hu, hm⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨matrices, hmat, he⟩ := Option.map_eq_some_iff.mp hm
  cases he
  obtain ⟨hgrid, hne⟩ := NonvanishingGrid.selectNonzero_sound hu
  obtain ⟨hMI, hIM, hlast⟩ := ProjectionMatrix.construct?_sound v M I hmat
  exact ⟨hgrid, hne, hMI, hIM, hlast⟩

omit [BEq E] [LawfulBEq E] in
/-- A homogeneous polynomial of positive degree cannot select the zero direction. -/
theorem direction_ne_zero_of_homogeneous (top : CMvPolynomial (r + 1) E) {b : ℕ}
    (hb : 0 < b) (htop : (fromCMvPolynomial top).IsHomogeneous b)
    (v : Fin (r + 1) → E) (hv : top.eval v ≠ 0) : v ≠ 0 := by
  intro he
  apply hv
  rw [he, eval_equiv, MvPolynomial.eval_zero]
  exact htop.coeff_eq_zero (by simpa using hb.ne)

/-- A long enough distinct scalar prefix makes the direction and matrix search succeed. -/
theorem choose?_exists (top : CMvPolynomial (r + 1) E) (values : List E) {b : ℕ}
    (hb : 0 < b) (htop : (fromCMvPolynomial top).IsHomogeneous b) (hne : top ≠ 0)
    (hdistinct : values.Nodup) (hsize : b < values.length) :
    ∃ v M I, choose? top values = some (v, M, I) := by
  obtain ⟨v, hv⟩ := NonvanishingGrid.selectNonzero_exists_of_nodup top values hne hdistinct
    (htop.totalDegree_le.trans_lt hsize)
  have hv0 := direction_ne_zero_of_homogeneous top hb htop v
    (NonvanishingGrid.selectNonzero_sound hv).2
  obtain ⟨M, I, hMI⟩ := ProjectionMatrix.construct?_exists v hv0
  exact ⟨v, M, I, by simp [choose?, hv, hMI]⟩

/-- The highest homogeneous component of a nonzero stored polynomial is nonzero. -/
theorem homogeneousPart_top_ne_zero (p : CMvPolynomial (r + 1) E) (hp : p ≠ 0) :
    homogeneousPart p.totalDegree p ≠ 0 := by
  classical
  have hn : fromCMvPolynomial p ≠ 0 := by
    intro he
    apply hp
    exact eq_iff_fromCMvPolynomial.mpr (by simpa using he)
  have hs := MvPolynomial.support_nonempty.mpr hn
  obtain ⟨m, hm, hd⟩ := Finset.exists_mem_eq_sup _ hs Finsupp.degree
  intro hz
  have he := congrArg (fun f : CMvPolynomial (r + 1) E =>
    MvPolynomial.coeff m (fromCMvPolynomial f)) hz
  rw [homogeneousPart_semantics, MvPolynomial.coeff_homogeneousComponent] at he
  have hd' : m.degree = p.totalDegree := hd.symm
  simp only [hd', if_pos, CPoly.map_zero, MvPolynomial.coeff_zero] at he
  exact MvPolynomial.mem_support_iff.mp hm he

/-- The whole direction search starts from the input polynomial, computing its top part. -/
def chooseFor? (p : CMvPolynomial (r + 1) E) (values : List E) :=
  choose? (homogeneousPart p.totalDegree p) values

/-- Nonconstant input and a sufficiently long distinct grid guarantee a computed direction. -/
theorem chooseFor?_exists (p : CMvPolynomial (r + 1) E) (values : List E)
    (hp : p ≠ 0) (hb : 0 < p.totalDegree) (hdistinct : values.Nodup)
    (hsize : p.totalDegree < values.length) :
    ∃ v M I, chooseFor? p values = some (v, M, I) := by
  apply choose?_exists _ _ hb
  · rw [homogeneousPart_semantics]
    exact MvPolynomial.homogeneousComponent_isHomogeneous _ _
  · exact homogeneousPart_top_ne_zero p hp
  · exact hdistinct
  · exact hsize

/-- For positive homogeneous degree, failure is exactly exhaustion of the scalar grid. -/
theorem choose?_eq_none_iff (top : CMvPolynomial (r + 1) E) (values : List E) {b : ℕ}
    (hb : 0 < b) (htop : (fromCMvPolynomial top).IsHomogeneous b) :
    choose? top values = none ↔ ∀ x, (∀ i, x i ∈ values) → top.eval x = 0 := by
  rw [← NonvanishingGrid.selectNonzero_eq_none_iff]
  cases hs : NonvanishingGrid.selectNonzero top values with
  | none => simp [choose?, hs]
  | some v =>
    have hv := direction_ne_zero_of_homogeneous top hb htop v
      (NonvanishingGrid.selectNonzero_sound hs).2
    obtain ⟨M, I, hm⟩ := ProjectionMatrix.construct?_exists v hv
    simp [choose?, hs, hm]

end ReedSolomon.HiddenDerivative.FastTaylor.Geometry.Direction
