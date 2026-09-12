/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Global.Provenance

/-! # Ring-valued affine Taylor residuals -/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.Global

open MvPolynomial PolynomialDifferential

variable {F A : Type*} [Field F] [CommRing A] {r : ℕ}

/-- Differential substitution in the Taylor coordinate over an arbitrary target ring. -/
noncomputable def ringResidual (f : F →+* A) (center : F) (Y : Polynomial A)
    (Q : DifferentialPolynomial F r) : Polynomial A :=
  eval₂Hom (Polynomial.C.comp f) (fun i =>
    i.elim (Polynomial.C (f center) + Polynomial.X)
      (fun j => Polynomial.hasseDeriv j.val Y)) Q

/-- The coefficient prefix, without any scalar inversions. -/
noncomputable def coefficientPrefix (Y : Polynomial A) (l : ℕ) : Polynomial A :=
  ∑ i : Fin l, Polynomial.monomial i.val (Y.coeff i.val)

@[simp] theorem coeff_coefficientPrefix (Y : Polynomial A) (l i : ℕ) :
    (coefficientPrefix Y l).coeff i = if i < l then Y.coeff i else 0 := by
  classical
  simp only [coefficientPrefix, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hi : i < l
  · rw [if_pos hi, Finset.sum_eq_single (⟨i, hi⟩ : Fin l)]
    · simp
    · intro j _ hj
      rw [if_neg]
      exact fun h => hj (Fin.ext h)
    · simp
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro h
    exact hi (h ▸ j.isLt)

/-- Evaluating the universal intercept is substitution of the coefficient prefix. -/
theorem eval₂_universalTaylorResidual_coeff (f : F →+* A) (center : F)
    (Y : Polynomial A) (Q : DifferentialPolynomial F r) (l h : ℕ) :
    eval₂ f (fun i : Fin l => Y.coeff i.val)
      ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff h) =
        (ringResidual f center (coefficientPrefix Y l) Q).coeff h := by
  let g := eval₂Hom f (fun i : Fin l => Y.coeff i.val)
  have he :
      ((Polynomial.mapRingHom g).comp (optionEquivLeft F (Fin l)).toRingHom).comp
        (aeval (fun i : Option (Fin (r + 1)) => i.elim (C center + X none)
          (fun j => universalTaylorJet l j.val))).toRingHom =
      eval₂Hom (Polynomial.C.comp f) (fun i : Option (Fin (r + 1)) =>
        i.elim (Polynomial.C (f center) + Polynomial.X)
          (fun j => Polynomial.hasseDeriv j.val (coefficientPrefix Y l))) := by
    apply ringHom_ext
    · intro a
      simp [g]
    · intro i
      cases i with
      | none => simp [g]
      | some j =>
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          aeval_X, eval₂Hom_X', Option.elim_some]
        change Polynomial.map g ((optionEquivLeft F (Fin l)) (universalTaylorJet l j.val)) =
          Polynomial.hasseDeriv j.val (coefficientPrefix Y l)
        rw [optionEquivLeft_universalTaylorJet, Polynomial.map_hasseDeriv]
        congr 1
        simp [universalTaylorPolynomial, coefficientPrefix, g, Polynomial.map_sum,
          Polynomial.map_monomial]
  have ht := congrArg (fun p : Polynomial A => p.coeff h) (DFunLike.congr_fun he Q)
  change ((Polynomial.map g (optionEquivLeft F (Fin l)
    (universalTaylorResidual l center Q))).coeff h) =
    (ringResidual f center (coefficientPrefix Y l) Q).coeff h at ht
  simpa only [Polynomial.coeff_map, g, coe_eval₂Hom] using ht

private theorem coeff_mul_of_X_pow_dvd (p q : Polynomial A) (k : ℕ)
    (hq : Polynomial.X ^ k ∣ q) : (p * q).coeff k = p.coeff 0 * q.coeff k := by
  obtain ⟨b, rfl⟩ := hq
  rw [show p * (Polynomial.X ^ k * b) = Polynomial.X ^ k * (p * b) by ring]
  simp [Polynomial.coeff_X_pow_mul']

private theorem prefix_jet_difference_dvd (Y : Polynomial A) (l j m : ℕ)
    (hm : m + j ≤ l) : Polynomial.X ^ m ∣
      Polynomial.hasseDeriv j Y - Polynomial.hasseDeriv j (coefficientPrefix Y l) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro i hi
  simp only [Polynomial.coeff_sub, Polynomial.hasseDeriv_coeff, coeff_coefficientPrefix,
    if_pos (by omega : i + j < l), sub_self]

private theorem prefix_jet_constant (Y : Polynomial A) (l : ℕ) (j : Fin (r + 1))
    (hl : r < l) : (Polynomial.hasseDeriv j.val (coefficientPrefix Y l)).coeff 0 =
      Y.coeff j.val := by
  simp [Polynomial.hasseDeriv_coeff, show j.val < l by omega]

/-- The first coefficient affected by a new Taylor coefficient is affine, including
when the coefficient ring is nonreduced. -/
theorem coeff_ringResidual_affine (f : F →+* A) (center : F)
    (Y : Polynomial A) (Q : DifferentialPolynomial F r) (l : ℕ) (hl : r < l) :
    (ringResidual f center Y Q).coeff (l - r) =
      eval₂ f (fun i : Fin l => Y.coeff i.val)
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r)) +
      (f (l.choose r : F) * Y.coeff l) *
        eval₂ f (fun i : Fin (r + 1) => Y.coeff i.val) (initialJetSeparant center Q) := by
  let a : Option (Fin (r + 1)) → Polynomial A := fun i =>
    i.elim (Polynomial.C (f center) + Polynomial.X)
      (fun j => Polynomial.hasseDeriv j.val (coefficientPrefix Y l))
  let d : Option (Fin (r + 1)) → Polynomial A := fun i =>
    i.elim 0 (fun j => Polynomial.hasseDeriv j.val Y -
      Polynomial.hasseDeriv j.val (coefficientPrefix Y l))
  have hpivot : Polynomial.X ^ (l - r) ∣ d (some (Fin.last r)) :=
    prefix_jet_difference_dvd Y l r (l - r) (by omega)
  have hother : ∀ i ∈ (Finset.univ : Finset (Option (Fin (r + 1)))),
      i ≠ some (Fin.last r) → Polynomial.X ^ (l - r + 1) ∣ d i := by
    intro i _ hi
    cases i with
    | none => simp [d]
    | some j =>
      apply prefix_jet_difference_dvd
      have hj : j.val ≠ r := by
        intro he
        apply hi
        congr 1
        exact Fin.ext he
      omega
  have ht := pow_succ_dvd_eval₂Hom_add_sub_pderiv (Polynomial.C.comp f) a d
    Finset.univ Q (some (Fin.last r)) Polynomial.X (l - r) (by omega)
    (Finset.mem_univ _) hpivot hother (by simp)
  have had : a + d = fun i : Option (Fin (r + 1)) =>
      i.elim (Polynomial.C (f center) + Polynomial.X)
        (fun j => Polynomial.hasseDeriv j.val Y) := by
    funext i
    cases i <;> simp [a, d]
  rw [had] at ht
  have hc := Polynomial.X_pow_dvd_iff.mp ht (l - r) (by omega)
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub,
    coeff_mul_of_X_pow_dvd _ _ _ hpivot] at hc
  have hdcoeff : (d (some (Fin.last r))).coeff (l - r) =
      f (l.choose r : F) * Y.coeff l := by
    simp [d, Polynomial.coeff_sub, Polynomial.hasseDeriv_coeff,
      show l - r + r = l by omega]
  have hsep : (eval₂Hom (Polynomial.C.comp f) a
      (pderiv (some (Fin.last r)) Q)).coeff 0 =
      eval₂ f (fun i : Fin (r + 1) => Y.coeff i.val) (initialJetSeparant center Q) := by
    have he : Polynomial.constantCoeff.comp (eval₂Hom (Polynomial.C.comp f) a) =
        (eval₂Hom f (fun i : Fin (r + 1) => Y.coeff i.val)).comp
          (aeval (fun i : Option (Fin (r + 1)) => i.elim (C center) X)).toRingHom := by
      apply ringHom_ext
      · intro b
        simp
      · intro i
        cases i with
        | none => simp [a]
        | some j => simpa [a] using prefix_jet_constant Y l j hl
    exact DFunLike.congr_fun he (pderiv (some (Fin.last r)) Q)
  rw [hdcoeff, hsep, sub_eq_zero, sub_eq_iff_eq_add] at hc
  rw [eval₂_universalTaylorResidual_coeff]
  simpa only [ringResidual, a, mul_comm, add_comm] using hc

/-- A vanishing actual residual coefficient supplies the recurrence needed by provenance. -/
theorem ringResidual_recurrence_of_coeff_eq_zero (f : F →+* A) (center : F)
    (Y : Polynomial A) (Q : DifferentialPolynomial F r) (l : ℕ) (hl : r < l)
    (hz : (ringResidual f center Y Q).coeff (l - r) = 0) :
    eval₂ f (fun i : Fin l => Y.coeff i.val)
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r)) +
      (f (l.choose r : F) * Y.coeff l) *
        eval₂ f (fun i : Fin (r + 1) => Y.coeff i.val) (initialJetSeparant center Q) = 0 := by
  rw [← coeff_ringResidual_affine f center Y Q l hl]
  exact hz

/-- Actual residual vanishing implies literal cleared-numerator provenance in the target ring. -/
theorem commonTaylorNumerator_of_ringResidual (f : F →+* A) (center : F)
    (Y : Polynomial A) (Q : DifferentialPolynomial F r) (K : ℕ)
    (hbin : ∀ l < K, r < l → (l.choose r : F) ≠ 0)
    (hzero : ∀ l < K, r < l → (ringResidual f center Y Q).coeff (l - r) = 0)
    (j : Fin K) :
    eval₂ f (fun i : Fin (r + 1) => Y.coeff i.val) (commonTaylorNumerator center Q K j) =
      eval₂ f (fun i : Fin (r + 1) => Y.coeff i.val) (initialJetSeparant center Q) ^
        (2 * K) * Y.coeff j.val := by
  let φ := eval₂Hom f (fun i : Fin (r + 1) => Y.coeff i.val)
  have hcomp : φ.comp C = f := by ext b; simp [φ]
  apply map_commonTaylorNumerator_two_mul center Q φ Y.coeff K _ hbin _ j
  · intro l _ hl
    simp [φ]
  · intro l hl hr
    rw [hcomp]
    exact ringResidual_recurrence_of_coeff_eq_zero f center Y Q l hr (hzero l hl hr)

end ReedSolomon.HiddenDerivative.FastTaylor.Global
