/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.TaylorReconstruction.UnivariateView
public import ArkLib.Data.Polynomial.ConfluentAlgebra.MonicArithmetic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Weighted coefficient bounds and monic reduction

The weight of a coefficient monomial is its parameter total degree plus its univariate
exponent. This is exactly ordinary total degree after flattening the final variable.
-/

@[expose] public section

namespace CPoly.TaylorReconstruction

open CompPoly

variable {E : Type*} [CommRing E] [DecidableEq E] [BEq E] [LawfulBEq E] [Nontrivial E]
variable {r : ℕ}

/-- A coefficient at exponent `i` has parameter degree at most `L-i`; zero coefficients
are permitted at every exponent. -/
def WeightedDegreeLE (p : CPolynomial (CMvPolynomial r E)) (L : ℕ) : Prop :=
  ∀ i, p.coeff i ≠ 0 → (fromCMvPolynomial (p.coeff i)).totalDegree + i ≤ L

/-- The stored last-variable view agrees with the standard first-variable equivalence after
rotating variable names. This is an equality of polynomials, not only of evaluations. -/
theorem splitLast_rotate (p : CMvPolynomial (r + 1) E) :
    (splitLast p).toPoly.map (polyRingEquiv (n := r) (R := E)).toRingHom =
      MvPolynomial.finSuccEquiv E r
        (MvPolynomial.rename (finRotate (r + 1)) (fromCMvPolynomial p)) := by
  rw [splitLast_toPoly, MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_rename]
  change (Polynomial.mapRingHom (polyRingEquiv (n := r) (R := E)).toRingHom)
    (MvPolynomial.eval₂ _ _ _) = _
  rw [MvPolynomial.eval₂_comp_left]
  change _ = MvPolynomial.eval₂
    (Polynomial.C.comp (MvPolynomial.C : E →+* MvPolynomial (Fin r) E))
    ((fun i : Fin (r + 1) => Fin.cases Polynomial.X
      (fun j => Polynomial.C (MvPolynomial.X j)) i) ∘ finRotate (r + 1))
    (fromCMvPolynomial p)
  congr 1
  · apply RingHom.ext
    intro a
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, Polynomial.coe_mapRingHom,
      Function.comp_apply, Polynomial.map_C, RingHom.coe_coe, Polynomial.C_inj]
    exact CMvPolynomial.fromCMvPolynomial_C a
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp only [RingEquiv.toRingHom_eq_coe, Polynomial.coe_mapRingHom, Function.comp_apply,
        Fin.lastCases_castSucc, Polynomial.map_C, RingHom.coe_coe, finRotate_apply,
        Fin.coeSucc_eq_succ, Fin.cases_succ, Polynomial.C_inj]
      exact CMvPolynomial.fromCMvPolynomial_X j

/-- Nonzero coefficients of the last-variable view obey the precise weighted degree bound. -/
theorem totalDegree_coeff_splitLast_add_le (p : CMvPolynomial (r + 1) E) (i : ℕ)
    (hi : (splitLast p).coeff i ≠ 0) :
    (fromCMvPolynomial ((splitLast p).coeff i)).totalDegree + i ≤
      (fromCMvPolynomial p).totalDegree := by
  have he := congrArg (fun q : Polynomial (MvPolynomial (Fin r) E) => q.coeff i)
    (splitLast_rotate p)
  simp only [Polynomial.coeff_map, ← CPolynomial.coeff_toPoly] at he
  have hn : (MvPolynomial.finSuccEquiv E r
      (MvPolynomial.rename (finRotate (r + 1)) (fromCMvPolynomial p))).coeff i ≠ 0 := by
    rw [← he]
    exact (map_ne_zero_iff _ (polyRingEquiv.injective)).mpr hi
  have hb := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le _ i hn
  rw [← he] at hb
  have hd := MvPolynomial.totalDegree_renameEquiv (R := E)
    (finRotate (r + 1)) (fromCMvPolynomial p)
  rw [MvPolynomial.renameEquiv_apply] at hd
  rw [hd] at hb
  exact hb

/-- A flat total-degree certificate supplies all weighted coefficient certificates. -/
theorem weightedDegreeLE_splitLast (p : CMvPolynomial (r + 1) E) {L : ℕ}
    (hp : (fromCMvPolynomial p).totalDegree ≤ L) : WeightedDegreeLE (splitLast p) L :=
  fun i hi => (totalDegree_coeff_splitLast_add_le p i hi).trans hp

omit [DecidableEq E] [Nontrivial E] in
/-- Every coefficient has parameter degree at most the full weighted bound, including zeros. -/
theorem totalDegree_coeff_le_of_weightedDegreeLE (p : CPolynomial (CMvPolynomial r E))
    {L : ℕ} (hp : WeightedDegreeLE p L) (i : ℕ) :
    (fromCMvPolynomial (p.coeff i)).totalDegree ≤ L := by
  by_cases hi : p.coeff i = 0
  · simp [hi]
  · exact (Nat.le_add_right _ _).trans (hp i hi)

omit [DecidableEq E] [Nontrivial E] in
/-- The usual subtraction form of the coefficient degree bound, valid also above the degree. -/
theorem totalDegree_coeff_le_sub (p : CPolynomial (CMvPolynomial r E)) {L : ℕ}
    (hp : WeightedDegreeLE p L) (i : ℕ) :
    (fromCMvPolynomial (p.coeff i)).totalDegree ≤ L - i := by
  by_cases hi : p.coeff i = 0
  · simp [hi]
  · exact Nat.le_sub_of_add_le (hp i hi)

/-- Weighted coefficient bounds also control the total degree of the flattened polynomial. -/
theorem totalDegree_flattenLast_le (p : CPolynomial (CMvPolynomial r E)) {L : ℕ}
    (hp : WeightedDegreeLE p L) : (fromCMvPolynomial (flattenLast p)).totalDegree ≤ L := by
  classical
  let f := MvPolynomial.rename (finRotate (r + 1)) (fromCMvPolynomial (flattenLast p))
  have he (i : ℕ) : fromCMvPolynomial (p.coeff i) =
      (MvPolynomial.finSuccEquiv E r f).coeff i := by
    have hh := congrArg (fun q : Polynomial (MvPolynomial (Fin r) E) => q.coeff i)
      (splitLast_rotate (flattenLast p))
    simp only [splitLast_flattenLast, Polynomial.coeff_map, ← CPolynomial.coeff_toPoly] at hh
    exact hh
  have hf : f.totalDegree ≤ L := by
    apply Finset.sup_le
    intro m hm
    have hs : m.tail ∈ ((MvPolynomial.finSuccEquiv E r f).coeff (m 0)).support := by
      apply MvPolynomial.mem_support_coeff_finSuccEquiv.mpr
      simpa only [Finsupp.cons_tail] using hm
    rw [← he] at hs
    have hn : p.coeff (m 0) ≠ 0 := by
      intro hz
      simp [hz] at hs
    have hd : m.degree = m.tail.degree + m 0 := by
      simp only [Finsupp.degree_eq_sum, Fin.sum_univ_succ]
      change m 0 + ∑ i : Fin r, m i.succ = (∑ i : Fin r, m i.succ) + m 0
      omega
    change m.degree ≤ L
    rw [hd]
    exact (Nat.add_le_add_right (MvPolynomial.le_totalDegree hs) _).trans (hp (m 0) hn)
  have hd := MvPolynomial.totalDegree_renameEquiv (R := E)
    (finRotate (r + 1)) (fromCMvPolynomial (flattenLast p))
  rw [MvPolynomial.renameEquiv_apply] at hd
  exact hd ▸ hf

/-- The coefficient weight is exactly total degree in the flat variable convention. -/
theorem weightedDegreeLE_iff_totalDegree_flattenLast
    (p : CPolynomial (CMvPolynomial r E)) (L : ℕ) :
    WeightedDegreeLE p L ↔ (fromCMvPolynomial (flattenLast p)).totalDegree ≤ L := by
  refine ⟨totalDegree_flattenLast_le p, fun h => ?_⟩
  simpa only [splitLast_flattenLast] using weightedDegreeLE_splitLast (flattenLast p) h

/-- Every coefficient of a flattened bounded polynomial has bounded parameter degree. -/
theorem totalDegree_coeff_le_of_flattenLast (p : CPolynomial (CMvPolynomial r E)) {L : ℕ}
    (hp : (fromCMvPolynomial (flattenLast p)).totalDegree ≤ L) (i : ℕ) :
    (fromCMvPolynomial (p.coeff i)).totalDegree ≤ L :=
  totalDegree_coeff_le_of_weightedDegreeLE p
    ((weightedDegreeLE_iff_totalDegree_flattenLast p L).mpr hp) i

private noncomputable def semanticFlatten :
    Polynomial (CMvPolynomial r E) →+* MvPolynomial (Fin (r + 1)) E :=
  (polyRingEquiv (n := r + 1) (R := E)).toRingHom.comp
    (flattenLast.comp CPolynomial.ringEquiv.symm.toRingHom)

private theorem semanticFlatten_toPoly (p : CPolynomial (CMvPolynomial r E)) :
    semanticFlatten p.toPoly = fromCMvPolynomial (flattenLast p) := by
  change fromCMvPolynomial (flattenLast (CPolynomial.ringEquiv.symm p.toPoly)) = _
  rw [← CPolynomial.ringEquiv_apply, RingEquiv.symm_apply_apply]

private theorem semanticFlatten_C (a : CMvPolynomial r E) :
    semanticFlatten (Polynomial.C a) = MvPolynomial.rename Fin.castSucc (fromCMvPolynomial a) := by
  rw [← CPolynomial.C_toPoly, semanticFlatten_toPoly, flattenLast_C]
  exact fromCMvPolynomial_rename Fin.castSucc a

private theorem semanticFlatten_X :
    semanticFlatten (Polynomial.X : Polynomial (CMvPolynomial r E)) =
      MvPolynomial.X (Fin.last r) := by
  rw [← CPolynomial.X_toPoly, semanticFlatten_toPoly, flattenLast_X]
  exact CMvPolynomial.fromCMvPolynomial_X _

private theorem coeff_degree_add_le (p : Polynomial (CMvPolynomial r E)) (i : ℕ)
    (hi : p.coeff i ≠ 0) :
    (fromCMvPolynomial (p.coeff i)).totalDegree + i ≤ (semanticFlatten p).totalDegree := by
  let q := CPolynomial.ringEquiv.symm p
  have hq : q.toPoly = p := by
    rw [← CPolynomial.ringEquiv_apply]
    exact CPolynomial.ringEquiv.apply_symm_apply p
  have hc : q.coeff i = p.coeff i := by rw [CPolynomial.coeff_toPoly, hq]
  rw [← hq, semanticFlatten_toPoly]
  have hw := weightedDegreeLE_splitLast (flattenLast q) le_rfl
  rw [splitLast_flattenLast] at hw
  simpa only [← CPolynomial.coeff_toPoly] using hw i (hc.symm ▸ hi)

private theorem semanticFlatten_mod_degree :
    ∀ (p : Polynomial (CMvPolynomial r E)) (h : Polynomial (CMvPolynomial r E))
      (_ : h.Monic) (_ : (semanticFlatten h).totalDegree ≤ h.natDegree),
      (semanticFlatten (p %ₘ h)).totalDegree ≤ (semanticFlatten p).totalDegree
  | p, h, hh, hw => by
    classical
    by_cases hd : h.degree ≤ p.degree ∧ p ≠ 0
    · have _wf := Polynomial.div_wf_lemma hd hh
      have hn : h.natDegree ≤ p.natDegree := Polynomial.natDegree_le_natDegree hd.1
      have hc := coeff_degree_add_le p p.natDegree
        (Polynomial.leadingCoeff_ne_zero.mpr hd.2)
      have hz : (semanticFlatten
          (h * (Polynomial.C p.leadingCoeff * Polynomial.X ^
            (p.natDegree - h.natDegree)))).totalDegree ≤
            (semanticFlatten p).totalDegree := by
        rw [_root_.map_mul, _root_.map_mul, _root_.map_pow, semanticFlatten_C, semanticFlatten_X]
        have hc' := MvPolynomial.totalDegree_rename_le Fin.castSucc
          (fromCMvPolynomial p.leadingCoeff)
        have hm := MvPolynomial.totalDegree_mul (semanticFlatten h)
          (MvPolynomial.rename Fin.castSucc (fromCMvPolynomial p.leadingCoeff) *
            MvPolynomial.X (Fin.last r) ^ (p.natDegree - h.natDegree))
        have hm' := MvPolynomial.totalDegree_mul
          (MvPolynomial.rename Fin.castSucc (fromCMvPolynomial p.leadingCoeff))
          (MvPolynomial.X (Fin.last r) ^ (p.natDegree - h.natDegree))
        rw [MvPolynomial.totalDegree_X_pow] at hm'
        change (fromCMvPolynomial p.leadingCoeff).totalDegree + p.natDegree ≤ _ at hc
        omega
      have hs : (semanticFlatten
          (p - h * (Polynomial.C p.leadingCoeff * Polynomial.X ^
            (p.natDegree - h.natDegree)))).totalDegree ≤
            (semanticFlatten p).totalDegree := by
        rw [_root_.map_sub]
        exact (MvPolynomial.totalDegree_sub _ _).trans (max_le le_rfl hz)
      have ih := semanticFlatten_mod_degree
        (p - h * (Polynomial.C p.leadingCoeff * Polynomial.X ^
          (p.natDegree - h.natDegree))) h hh hw
      have he : p %ₘ h =
          (p - h * (Polynomial.C p.leadingCoeff * Polynomial.X ^
            (p.natDegree - h.natDegree))) %ₘ h := by
        conv_lhs => unfold Polynomial.modByMonic Polynomial.divModByMonicAux
        simp only [dif_pos hh, dif_pos hd]
        rw [Polynomial.modByMonic, dif_pos hh]
      rw [he]
      exact ih.trans hs
    · unfold Polynomial.modByMonic Polynomial.divModByMonicAux
      simp only [dif_pos hh, dif_neg hd, le_refl]
  termination_by p => p

/-- The executable monic remainder preserves ordinary total degree whenever the divisor
has the coefficient weights of a monic projection. -/
theorem weightedDegreeLE_modByMonic (p h : CPolynomial (CMvPolynomial r E))
    (hh : h.monic) (hw : WeightedDegreeLE h h.natDegree) {L : ℕ}
    (hp : WeightedDegreeLE p L) : WeightedDegreeLE (p.modByMonic h) L := by
  apply (weightedDegreeLE_iff_totalDegree_flattenLast _ _).mpr
  have hh' : h.toPoly.Monic := (CPolynomial.monic_toPoly_iff h).mp hh
  have hw' : (semanticFlatten h.toPoly).totalDegree ≤ h.toPoly.natDegree := by
    rw [semanticFlatten_toPoly, ← CPolynomial.natDegree_toPoly]
    exact totalDegree_flattenLast_le h hw
  have hr := semanticFlatten_mod_degree p.toPoly h.toPoly hh' hw'
  rw [← CPolynomial.modByMonic_toPoly_eq_modByMonic p h hh,
    semanticFlatten_toPoly, semanticFlatten_toPoly] at hr
  exact hr.trans (totalDegree_flattenLast_le p hp)

end CPoly.TaylorReconstruction
