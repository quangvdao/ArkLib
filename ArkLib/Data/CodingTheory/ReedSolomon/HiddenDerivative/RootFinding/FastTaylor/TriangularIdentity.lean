/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.MvPolynomial.FirstOrderTaylor
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Tactic

/-!
# Ring-valued triangular Hasse-jet coefficient identity

The source equation is already shifted to the local independent variable and
may have coefficients in a nonreduced commutative ring. Variables are ordered
`Z,Y₀,…,Yᵣ`. The result is finite and imposes no infinite-solution hypothesis.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.TriangularIdentity

open MvPolynomial Polynomial

variable {A : Type*} [CommRing A] {r : ℕ}

/-- Substitute the local independent variable and all Hasse derivatives. -/
noncomputable def residual (T : MvPolynomial (Fin (r + 2)) A) (Y : Polynomial A) :
    Polynomial A := eval₂Hom Polynomial.C (Fin.cases Polynomial.X
      (fun j : Fin (r + 1) => Polynomial.hasseDeriv j.val Y)) T

/-- The exact polynomial coefficient prefix. -/
noncomputable def prefixPolynomial (Y : Polynomial A) (l : ℕ) : Polynomial A :=
  ∑ i : Fin l, Polynomial.monomial i.val (Y.coeff i.val)

@[simp] theorem coeff_prefixPolynomial (Y : Polynomial A) (l i : ℕ) :
    (prefixPolynomial Y l).coeff i = if i < l then Y.coeff i else 0 := by
  classical
  simp only [prefixPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
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
    exact fun h => hi (h ▸ j.isLt)

/-- The initial separant is the highest-variable partial at the supplied initial jet. -/
noncomputable def separant (T : MvPolynomial (Fin (r + 2)) A) (initial : Fin (r + 1) → A) : A :=
  eval₂Hom (RingHom.id A) (Fin.cases 0 initial) (pderiv (Fin.last (r + 1)) T)

private theorem jet_difference_dvd (Y : Polynomial A) (l j m : ℕ)
    (hm : m + j ≤ l) : Polynomial.X ^ m ∣
      Polynomial.hasseDeriv j Y - Polynomial.hasseDeriv j (prefixPolynomial Y l) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro i hi
  simp only [Polynomial.coeff_sub, Polynomial.hasseDeriv_coeff, coeff_prefixPolynomial,
    if_pos (by omega : i + j < l), sub_self]

private theorem coeff_mul_of_dvd (p q : Polynomial A) (k : ℕ)
    (hq : Polynomial.X ^ k ∣ q) : (p * q).coeff k = p.coeff 0 * q.coeff k := by
  obtain ⟨b, rfl⟩ := hq
  rw [show p * (Polynomial.X ^ k * b) = Polynomial.X ^ k * (p * b) by ring]
  simp [Polynomial.coeff_X_pow_mul']

/-- The current residual coefficient is affine in the newly introduced Taylor coefficient. -/
theorem coefficient_affine (T : MvPolynomial (Fin (r + 2)) A) (Y : Polynomial A)
    (l : ℕ) (hl : r < l) :
    (residual T Y).coeff (l - r) =
      (residual T (prefixPolynomial Y l)).coeff (l - r) +
      ((l.choose r : A) * Y.coeff l) * separant T (fun j => Y.coeff j.val) := by
  let a : Fin (r + 2) → Polynomial A := Fin.cases Polynomial.X
    (fun j => Polynomial.hasseDeriv j.val (prefixPolynomial Y l))
  let delta : Fin (r + 2) → Polynomial A := Fin.cases 0
    (fun j => Polynomial.hasseDeriv j.val Y -
      Polynomial.hasseDeriv j.val (prefixPolynomial Y l))
  have hpivot : Polynomial.X ^ (l - r) ∣ delta (Fin.last (r + 1)) := by
    change Polynomial.X ^ (l - r) ∣
      Polynomial.hasseDeriv r Y - Polynomial.hasseDeriv r (prefixPolynomial Y l)
    exact jet_difference_dvd Y l r (l - r) (by omega)
  have hother : ∀ i ∈ (Finset.univ : Finset (Fin (r + 2))),
      i ≠ Fin.last (r + 1) → Polynomial.X ^ (l - r + 1) ∣ delta i := by
    intro i _ hi
    cases i using Fin.cases with
    | zero => simp [delta]
    | succ j =>
      change Polynomial.X ^ (l - r + 1) ∣
        Polynomial.hasseDeriv j.val Y - Polynomial.hasseDeriv j.val (prefixPolynomial Y l)
      apply jet_difference_dvd
      have hj : j.val ≠ r := by
        intro h
        apply hi
        exact Fin.ext (by simp [h])
      omega
  have ht := pow_succ_dvd_eval₂Hom_add_sub_pderiv Polynomial.C a delta Finset.univ T
    (Fin.last (r + 1)) Polynomial.X (l - r) (by omega) (Finset.mem_univ _)
    hpivot hother (by simp)
  have had : a + delta = Fin.cases Polynomial.X
      (fun j : Fin (r + 1) => Polynomial.hasseDeriv j.val Y) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [a, delta]
  rw [had] at ht
  have hc := Polynomial.X_pow_dvd_iff.mp ht (l - r) (by omega)
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub, coeff_mul_of_dvd _ _ _ hpivot] at hc
  have hdcoeff : (delta (Fin.last (r + 1))).coeff (l - r) =
      (l.choose r : A) * Y.coeff l := by
    change (Polynomial.hasseDeriv r Y -
      Polynomial.hasseDeriv r (prefixPolynomial Y l)).coeff (l - r) = _
    simp [Polynomial.coeff_sub, Polynomial.hasseDeriv_coeff, show l - r + r = l by omega]
  have hsep : (eval₂Hom Polynomial.C a (pderiv (Fin.last (r + 1)) T)).coeff 0 =
      separant T (fun j => Y.coeff j.val) := by
    have he : Polynomial.constantCoeff.comp (eval₂Hom Polynomial.C a) =
        eval₂Hom (RingHom.id A) (Fin.cases 0 (fun j : Fin (r + 1) => Y.coeff j.val)) := by
      apply MvPolynomial.ringHom_ext
      · intro b
        simp
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [a]
        · simp [a, Polynomial.hasseDeriv_coeff, show j.val < l by omega]
    exact DFunLike.congr_fun he (pderiv (Fin.last (r + 1)) T)
  rw [hdcoeff, hsep, sub_eq_zero, sub_eq_iff_eq_add] at hc
  simpa only [residual, a, mul_comm, add_comm] using hc

end ReedSolomon.HiddenDerivative.FastTaylor.TriangularIdentity
