/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.SharpRatio
import ArkLib.ToMathlib.Set.Finite

/-!
# Dimension-sensitive agreement incidence

The usual sharp incidence induction uses one fixed upper bound on the number of equations that
may contain a positive-dimensional component.  In coefficient spaces, the sharper hereditary
statement depends on the component dimension: a component of dimension `t` can be contained in
at most `k - t` independent equations.  Recording that bound at every retained principal cut
replaces a power of one worst-case ratio by a product of the ratios at the actual dimensions.

This module isolates the generic induction.  Applications must prove the hereditary component
hypothesis on their actual retained source locus; the theorem does not assume a target dimension
bound merely from pointwise uniqueness.
-/

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

/-- The product of the successive incidence ratios in dimensions `1, ..., d`.

The factor `b` is the degree bound for each cutting equation.  For affine hyperplanes, specialize
to `b = 1` to obtain the product used for Reed--Solomon evaluation incidence. -/
def dimensionSensitiveIncidenceProduct (n A k b : ℕ) : ℕ → ℚ
  | 0 => 1
  | d + 1 => dimensionSensitiveIncidenceProduct n A k b d *
      ((((n - k + d + 1) * b : ℕ) : ℚ) / ((A - k + d + 1 : ℕ) : ℚ))

@[simp]
theorem dimensionSensitiveIncidenceProduct_zero (n A k b : ℕ) :
    dimensionSensitiveIncidenceProduct n A k b 0 = 1 := rfl

theorem dimensionSensitiveIncidenceProduct_succ (n A k b d : ℕ) :
    dimensionSensitiveIncidenceProduct n A k b (d + 1) =
      dimensionSensitiveIncidenceProduct n A k b d *
        ((((n - k + d + 1) * b : ℕ) : ℚ) /
          ((A - k + d + 1 : ℕ) : ℚ)) := rfl

theorem dimensionSensitiveIncidenceProduct_nonneg (n A k b d : ℕ) :
    0 ≤ dimensionSensitiveIncidenceProduct n A k b d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [dimensionSensitiveIncidenceProduct_succ]
      exact mul_nonneg ih (div_nonneg (by positivity) (by positivity))

/-- The ratio of proper cuts at dimension `d` is controlled by the dimension-`d` factor
when at most `k - d` cuts vanish identically. -/
theorem goodCuts_div_agreements_le_dimension
    {n A k d m : ℕ} (hd : 0 < d) (hdk : d ≤ k) (hm : m ≤ k - d)
    (hkA : k ≤ A) (hAn : A ≤ n) :
    ((n - m : ℕ) : ℚ) / ((A - m : ℕ) : ℚ) ≤
      ((n - k + d : ℕ) : ℚ) / ((A - k + d : ℕ) : ℚ) := by
  have hm' : m < (k - d) + 1 := by omega
  have hk' : (k - d) + 1 ≤ A := by omega
  have hratio := goodCuts_div_agreements_le hm' hk' hAn
  simpa only [show n - (k - d + 1) + 1 = n - k + d by omega,
    show A - (k - d + 1) + 1 = A - k + d by omega] using hratio

/-- Incidence with an explicit current dimension and a hereditary dimension-sensitive bound
on identically vanishing cuts. -/
private theorem affineAgreementIncidence_bound_dimensionSensitive_aux
    {n A k b d : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k ∧
        (cutsInIdeal Q cuts).card ≤ k - (hilbertPolynomial Q).natDegree)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ zeroLocus F P ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card)
    (hd : (hilbertPolynomial P).natDegree = d) :
    (S.card : ℚ) ≤ affineDegree P * dimensionSensitiveIncidenceProduct n A k b d := by
  classical
  induction d using Nat.strong_induction_on generalizing P S with
  | h d ih =>
      cases d with
      | zero =>
          have ht := finite_zeroLocus_and_ncard_le_affineDegree (F := F) (E := F) P hd
          have hc : S.card ≤ (zeroLocus F P).ncard := by
            simpa using Set.ncard_le_ncard (fun x hx ↦ (hS x hx).1) ht.1
          have hc' : (S.card : ℚ) ≤ ((zeroLocus F P).ncard : ℚ) := by
            exact_mod_cast hc
          simpa using hc'.trans ht.2
      | succ e =>
          let Bad := cutsInIdeal P cuts
          let good := Finset.univ.filter fun i ↦ i ∉ Bad
          let R : ℚ := (((n - k + e + 1) * b : ℕ) : ℚ) /
            ((A - k + e + 1 : ℕ) : ℚ)
          have hdpos : 0 < (hilbertPolynomial P).natDegree := by rw [hd]; omega
          have hPcomponent := hcomponent P le_rfl hP hs hdpos
          have hed : e + 1 ≤ k := by simpa only [hd] using hPcomponent.1
          have hBad : Bad.card ≤ k - (e + 1) := by
            simpa only [Bad, hd] using hPcomponent.2
          have hlowerNat : S.card * (A - Bad.card) ≤
              ∑ i ∈ good, (cutPoints S (cuts i)).card := by
            exact finiteAgreementIncidence_lower_sharp S Bad
              (fun x i ↦ aeval x (cuts i) = 0) (fun x hx ↦ hA x hx)
          have hlower : (S.card : ℚ) * (A - Bad.card : ℕ) ≤
              ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) := by
            exact_mod_cast hlowerNat
          have hchild : ∀ i, cuts i ∉ P →
              ∀ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                ((componentPoints S Q).card : ℚ) ≤ affineDegree Q *
                  dimensionSensitiveIncidenceProduct n A k b e := by
            intro i hiP Q hQ
            have hQdata := (Ideal.mem_retainedMinimalPrimes _ _ _).mp hQ
            have hQP : P ≤ Q := le_sup_left.trans hQdata.1.le
            have hQdegree : (hilbertPolynomial Q).natDegree = e := by
              have hpure := principalCut_component_hilbertPolynomial_natDegree_add_one
                hP hiP hQdata.1
              rw [hd] at hpure
              omega
            apply ih e (by omega) (P := Q) (S := componentPoints S Q)
              hQdata.1.isPrime hQdata.2
            · intro J hQJ hJ hsJ hdJ
              exact hcomponent J (hQP.trans hQJ) hJ hsJ hdJ
            · intro x hx
              rw [mem_componentPoints] at hx
              exact ⟨hx.2, (hS x hx.1).2⟩
            · intro x hx
              rw [mem_componentPoints] at hx
              exact hA x hx.1
            · exact hQdegree
          have hone (i : Fin n) (hi : i ∈ good) :
              ((cutPoints S (cuts i)).card : ℚ) ≤
                b * affineDegree P * dimensionSensitiveIncidenceProduct n A k b e := by
            have hiP : cuts i ∉ P := by
              simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and,
                Bad, mem_cutsInIdeal] using hi
            have hc := card_filter_cut_le_sum_retained P s (cuts i) S hS
            have hsdeg := sum_retained_affineDegree_le (s := s) hP hiP (hdeg i)
            calc
              ((cutPoints S (cuts i)).card : ℚ) ≤
                  ∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    ((componentPoints S Q).card : ℚ) := by exact_mod_cast hc
              _ ≤ ∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    affineDegree Q * dimensionSensitiveIncidenceProduct n A k b e :=
                Finset.sum_le_sum (fun Q hQ ↦ hchild i hiP Q hQ)
              _ = (∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    affineDegree Q) * dimensionSensitiveIncidenceProduct n A k b e := by
                rw [Finset.sum_mul]
              _ ≤ ((b : ℚ) * affineDegree P) *
                    dimensionSensitiveIncidenceProduct n A k b e :=
                mul_le_mul_of_nonneg_right hsdeg
                  (dimensionSensitiveIncidenceProduct_nonneg n A k b e)
              _ = (b : ℚ) * affineDegree P *
                    dimensionSensitiveIncidenceProduct n A k b e := rfl
          have hgoodcard : good.card = n - Bad.card := by
            rw [show good = Finset.univ \ Bad by ext i; simp [good]]
            rw [Finset.card_sdiff]
            simp
          have hupper : ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) ≤
              ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P *
                dimensionSensitiveIncidenceProduct n A k b e) := by
            calc
              _ ≤ ∑ _i ∈ good, ((b : ℚ) * affineDegree P *
                    dimensionSensitiveIncidenceProduct n A k b e) :=
                Finset.sum_le_sum hone
              _ = _ := by simp [hgoodcard]
          have hden : (0 : ℚ) < (A - Bad.card : ℕ) := by
            exact_mod_cast Nat.sub_pos_of_lt (hBad.trans_lt (by omega : k - (e + 1) < A))
          have hratio := goodCuts_div_agreements_le_dimension (by omega) hed hBad hkA hAn
          have hlocal : ((n - Bad.card : ℕ) : ℚ) * b ≤
              R * (A - Bad.card : ℕ) := by
            refine (div_le_iff₀ hden).mp ?_
            dsimp only [R]
            calc
              ((n - Bad.card : ℕ) : ℚ) * b / (A - Bad.card : ℕ) =
                  (b : ℚ) * (((n - Bad.card : ℕ) : ℚ) /
                    (A - Bad.card : ℕ)) := by ring
              _ ≤ (b : ℚ) * (((n - k + e + 1 : ℕ) : ℚ) /
                    (A - k + e + 1 : ℕ)) :=
                mul_le_mul_of_nonneg_left hratio (by positivity)
              _ = (((n - k + e + 1) * b : ℕ) : ℚ) /
                    (A - k + e + 1 : ℕ) := by
                rw [Nat.cast_mul]
                ring
          apply le_of_mul_le_mul_right _ hden
          calc
            (S.card : ℚ) * (A - Bad.card : ℕ) ≤
                ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) := hlower
            _ ≤ ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P *
                  dimensionSensitiveIncidenceProduct n A k b e) := hupper
            _ ≤ (affineDegree P * dimensionSensitiveIncidenceProduct n A k b (e + 1)) *
                  (A - Bad.card : ℕ) := by
              rw [dimensionSensitiveIncidenceProduct_succ]
              calc
                ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P *
                    dimensionSensitiveIncidenceProduct n A k b e) =
                    (((n - Bad.card : ℕ) : ℚ) * b) *
                      (affineDegree P *
                        dimensionSensitiveIncidenceProduct n A k b e) := by ring
                _ ≤ (R * (A - Bad.card : ℕ)) *
                      (affineDegree P *
                        dimensionSensitiveIncidenceProduct n A k b e) :=
                  mul_le_mul_of_nonneg_right hlocal
                    (mul_nonneg (affineDegree_nonneg P)
                      (dimensionSensitiveIncidenceProduct_nonneg n A k b e))
                _ = (affineDegree P *
                      (dimensionSensitiveIncidenceProduct n A k b e * R)) *
                    (A - Bad.card : ℕ) := by ring

/-- A finite set on an affine principal-open component satisfies the dimension-sensitive
product bound once the component bound on identically vanishing cuts is proved hereditarily. -/
theorem affineAgreementIncidence_bound_dimensionSensitive
    {n A k b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k ∧
        (cutsInIdeal Q cuts).card ≤ k - (hilbertPolynomial Q).natDegree)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ zeroLocus F P ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ affineDegree P *
      dimensionSensitiveIncidenceProduct n A k b (hilbertPolynomial P).natDegree := by
  exact affineAgreementIncidence_bound_dimensionSensitive_aux hP hs cuts hdeg hkA hAn
    hcomponent S hS hA rfl

/-- The full agreement locus on a principal-open prime component is finite and satisfies the
same dimension-sensitive bound as each of its finite subsets.  This is the form needed before
projecting a retained source family to its challenge coordinates. -/
theorem finite_agreementLocus_and_ncard_le_dimensionSensitive
    {n A k b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k ∧
        (cutsInIdeal Q cuts).card ≤ k - (hilbertPolynomial Q).natDegree) :
    let T := {x : σ → F | x ∈ principalOpenZeroLocus P s ∧
      A ≤ (agreementIndices cuts x).card}
    T.Finite ∧ (T.ncard : ℚ) ≤ affineDegree P *
      dimensionSensitiveIncidenceProduct n A k b (hilbertPolynomial P).natDegree := by
  classical
  dsimp only
  let T := {x : σ → F | x ∈ principalOpenZeroLocus P s ∧
    A ≤ (agreementIndices cuts x).card}
  have hbound (S : Finset (σ → F)) (hST : (S : Set (σ → F)) ⊆ T) :
      (S.card : ℚ) ≤ affineDegree P *
        dimensionSensitiveIncidenceProduct n A k b (hilbertPolynomial P).natDegree := by
    apply affineAgreementIncidence_bound_dimensionSensitive hP hs cuts hdeg hkA hAn
      hcomponent S
    · intro x hx
      exact (hST hx).1
    · intro x hx
      exact (hST hx).2
  have hfinite : T.Finite := Set.finite_of_forall_finset_card_le hbound
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card T hfinite]
  exact hbound hfinite.toFinset (fun _ hx ↦ hfinite.mem_toFinset.mp hx)

end AffineHilbert
