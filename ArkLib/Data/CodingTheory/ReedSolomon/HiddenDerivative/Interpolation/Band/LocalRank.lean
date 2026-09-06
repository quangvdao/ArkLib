/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Band.Basic
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.IntermediateSpace


/-!
# Actual local support of the asymmetric band

This file implements the reachable-coordinate argument of [Dao, Kominers, Thaler, and Zheng,
*Reed--Solomon List Decoding and Mutual Correlated Agreement up to Capacity*][DKTZ26], equation
(36) (`eq:band-reachable-coordinates`).
The map is the existing `localConstraintAt`, with the error occurring as `TE` and retained
contact order `i+d*h<m`. The support argument works directly at arbitrary received points.

The private signed-weight support helpers are adapted from `LocalIntermediateSpace.lean`,
which credits Kai Zhe Zheng's authorized `rs-ld-mca` source at
`9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`. No characteristic restriction is used.
-/

open PolynomialDifferential


noncomputable section

open scoped BigOperators Pointwise

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

section SupportWeights

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
variable {σ τ : Type*}

omit [PartialOrder M] [IsOrderedAddMonoid M] in
private theorem support_weight_C_eq_zero (w : τ → M) (a : R)
    {e : τ →₀ ℕ} (he : e ∈ (C a : MvPolynomial τ R).support) :
    Finsupp.weight w e = 0 := by
  classical
  have he' : e ∈ ({0} : Finset (τ →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset he
  have : e = 0 := Finset.mem_singleton.mp he'
  subst e
  exact map_zero (Finsupp.weight w)

omit [PartialOrder M] [IsOrderedAddMonoid M] in
private theorem support_weight_X_eq (w : τ → M) (i : τ)
    {e : τ →₀ ℕ} (he : e ∈ (X i : MvPolynomial τ R).support) :
    Finsupp.weight w e = w i := by
  classical
  have he' : e ∈ ({Finsupp.single i 1} : Finset (τ →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset he
  have : e = Finsupp.single i 1 := Finset.mem_singleton.mp he'
  subst e
  rw [Finsupp.weight_single]
  exact one_nsmul (w i)

omit [IsOrderedAddMonoid M] in
private theorem support_weight_add_le (w : τ → M)
    {P Q : MvPolynomial τ R} {a : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a)
    (hQ : ∀ e ∈ Q.support, Finsupp.weight w e ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (P + Q).support) :
    Finsupp.weight w e ≤ a := by
  classical
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with heP | heQ
  · exact hP e heP
  · exact hQ e heQ

omit [IsOrderedAddMonoid M] in
private theorem support_weight_sum_le (w : τ → M)
    {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial τ R) {a : M}
    (hP : ∀ i ∈ s, ∀ e ∈ (P i).support, Finsupp.weight w e ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (s.sum P).support) :
    Finsupp.weight w e ≤ a := by
  classical
  have he' := MvPolynomial.support_sum he
  rcases Finset.mem_biUnion.mp he' with ⟨i, hi, hei⟩
  exact hP i hi e hei

private theorem support_weight_mul_le (w : τ → M)
    {P Q : MvPolynomial τ R} {a b : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a)
    (hQ : ∀ e ∈ Q.support, Finsupp.weight w e ≤ b)
    {e : τ →₀ ℕ} (he : e ∈ (P * Q).support) :
    Finsupp.weight w e ≤ a + b := by
  classical
  have he' : e ∈ P.support + Q.support := MvPolynomial.support_mul P Q he
  rcases Finset.mem_add.mp he' with ⟨eP, heP, eQ, heQ, rfl⟩
  simpa using add_le_add (hP eP heP) (hQ eQ heQ)

private theorem support_weight_pow_le (w : τ → M)
    {P : MvPolynomial τ R} {a : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a) (n : ℕ)
    {e : τ →₀ ℕ} (he : e ∈ (P ^ n).support) :
    Finsupp.weight w e ≤ n • a := by
  induction n generalizing e with
  | zero =>
      simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | succ n ih =>
      rw [pow_succ] at he
      simpa [succ_nsmul] using support_weight_mul_le w
        (fun e he => ih he) hP he

private theorem support_weight_prod_le (w : τ → M)
    {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial τ R) (a : ι → M)
    (hP : ∀ i ∈ s, ∀ e ∈ (P i).support, Finsupp.weight w e ≤ a i)
    {e : τ →₀ ℕ} (he : e ∈ (s.prod P).support) :
    Finsupp.weight w e ≤ s.sum a := by
  classical
  induction s using Finset.induction_on generalizing e with
  | empty =>
      simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi] at he
      rw [Finset.sum_insert hi]
      exact support_weight_mul_le w
        (hP i (Finset.mem_insert_self i s))
        (fun e he => ih
          (fun j hj => hP j (Finset.mem_insert_of_mem hj)) he) he

/-- Substitution cannot increase a support weight if every substituted
variable has support weight at most the weight assigned to that variable. -/
private theorem support_weight_bind₁_le (wSource : σ → M) (wTarget : τ → M)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, ∀ e ∈ (f i).support,
      Finsupp.weight wTarget e ≤ wSource i)
    {P : MvPolynomial σ R} {a : M}
    (hP : ∀ u ∈ P.support, Finsupp.weight wSource u ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (MvPolynomial.bind₁ f P).support) :
    Finsupp.weight wTarget e ≤ a := by
  classical
  rw [MvPolynomial.as_sum P, map_sum] at he
  have he' := MvPolynomial.support_sum he
  rcases Finset.mem_biUnion.mp he' with ⟨u, hu, heu⟩
  rw [MvPolynomial.bind₁_monomial] at heu
  have hprod : ∀ v ∈ (u.support.prod fun i => f i ^ u i).support,
      Finsupp.weight wTarget v ≤ Finsupp.weight wSource u := by
    intro v hv
    simpa only [Finsupp.weight_apply, Finsupp.sum] using
      (support_weight_prod_le wTarget u.support
        (fun i => f i ^ u i) (fun i => u i • wSource i)
        (fun i hi v hv => support_weight_pow_le wTarget (hf i) (u i) hv) hv)
  have hmul := support_weight_mul_le wTarget
    (a := (0 : M)) (b := Finsupp.weight wSource u)
    (fun v hv => le_of_eq (support_weight_C_eq_zero wTarget _ hv))
    hprod heu
  have hmono : Finsupp.weight wTarget e ≤ Finsupp.weight wSource u := by
    simpa using hmul
  exact hmono.trans (hP u hu)

end SupportWeights


variable {R : Type*} [CommRing R] {d D m W Cmin Cmax : ℕ} {L : ℝ}

/-- Total degree in the error and visible jets, omitting `T`. -/
def bandLocalJetDegree (e : LocalVariable d →₀ ℕ) : ℕ := Finsupp.degree e.some

/-- Ordinary degree in the visible jets `Y₂,...,Y_d`. -/
def bandLocalHigherDegree (e : LocalVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (fun v ↦ match v with
    | some (some j) => if 1 ≤ j.val then 1 else 0
    | _ => 0) e

private def bandLocalWeight (t aux : ℤ) (jets : Fin d → ℤ) : LocalVariable d → ℤ
  | none => t
  | some none => aux
  | some (some j) => jets j

private def bandSourceWeight (x y : ℤ) (jets : Fin d → ℤ) : JetVariable d → ℤ
  | none => x
  | some j => Fin.cases y jets j

private theorem unscaled_generator_weight_le (t aux x y : ℤ) (jets : Fin d → ℤ)
    (ht : t ≤ x) (hx : 0 ≤ x) (hy : 0 ≤ y) (haux : t + aux ≤ y)
    (hjets : ∀ j : Fin d, (j.val + 1) • t + jets j ≤ y)
    (center received : R) (v : JetVariable d) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalImage d center received v).support) :
    Finsupp.weight (bandLocalWeight t aux jets) e ≤ bandSourceWeight x y jets v := by
  rcases v with _ | j
  · apply support_weight_add_le _ ?_ ?_ he
    · intro z hz
      simpa [support_weight_C_eq_zero _ _ hz, bandSourceWeight] using hx
    · intro z hz
      simpa [support_weight_X_eq _ _ hz, bandLocalWeight, localT, bandSourceWeight] using ht
  · induction j using Fin.cases with
    | zero =>
      apply support_weight_add_le _ ?_ ?_ he
      · apply support_weight_add_le _
        · intro z hz
          simpa [support_weight_C_eq_zero _ _ hz, bandSourceWeight] using hy
        · intro z hz
          rw [localCorrection] at hz
          apply support_weight_sum_le _ Finset.univ _ (a := y) ?_ hz
          intro j hj z hz
          have h := support_weight_mul_le (bandLocalWeight t aux jets)
            (a := (j.val + 1) • t) (b := jets j)
            (fun v hv ↦ by
              have hp := support_weight_mul_le (bandLocalWeight t aux jets)
                (a := 0) (b := (j.val + 1) • t)
                (fun w hw ↦ (support_weight_C_eq_zero _ _ hw).le)
                (fun w hw ↦ support_weight_pow_le _
                  (fun q hq ↦ by simpa [bandLocalWeight, localT] using
                    (support_weight_X_eq (bandLocalWeight t aux jets) (localT d) hq).le)
                  (j.val + 1) hw) hv
              simpa using hp)
            (fun v hv ↦ by simpa [bandLocalWeight, localY] using
              (support_weight_X_eq (bandLocalWeight t aux jets) (localY j) hv).le) hz
          exact h.trans (hjets j)
      · intro z hz
        have h := support_weight_mul_le (bandLocalWeight t aux jets)
          (a := t) (b := aux)
          (fun v hv ↦ by simpa [bandLocalWeight, localT] using
            (support_weight_X_eq (bandLocalWeight t aux jets) (localT d) hv).le)
          (fun v hv ↦ by simpa [bandLocalWeight, localE, localAux] using
            (support_weight_X_eq (bandLocalWeight t aux jets) (localE d) hv).le) hz
        exact h.trans haux
    | succ j =>
      simpa [unscaledLocalImage, bandSourceWeight, bandLocalWeight, localY] using
        (support_weight_X_eq (bandLocalWeight t aux jets) (localY j) he).le

private theorem unscaled_support_weight_le (t aux x y : ℤ) (jets : Fin d → ℤ)
    (ht : t ≤ x) (hx : 0 ≤ x) (hy : 0 ≤ y) (haux : t + aux ≤ y)
    (hjets : ∀ j : Fin d, (j.val + 1) • t + jets j ≤ y)
    (center received : R) {Q : DifferentialPolynomial R d} {cap : ℤ}
    (hQ : ∀ u ∈ Q.support, Finsupp.weight (bandSourceWeight x y jets) u ≤ cap)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    Finsupp.weight (bandLocalWeight t aux jets) e ≤ cap :=
  support_weight_bind₁_le _ _ _
    (unscaled_generator_weight_le t aux x y jets ht hx hy haux hjets center received) hQ he

private theorem band_weight_source_higher (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (bandSourceWeight 0 0 (fun j : Fin d ↦ (j.val : ℤ))) u =
      (fullHigherJetWeight u : ℤ) := by
  simp only [Finsupp.weight_eq_sum, fullHigherJetWeight, Fintype.sum_option,
    bandSourceWeight, nsmul_eq_mul, mul_zero, zero_add]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp

private theorem band_weight_source_total (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (bandSourceWeight 0 1 (fun _ : Fin d ↦ 1)) u =
      (totalJetDegree u : ℤ) := by
  simp only [Finsupp.weight_eq_sum, totalJetDegree, Finsupp.degree_eq_sum,
    Fintype.sum_option, bandSourceWeight, nsmul_eq_mul, mul_zero, zero_add]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp

private theorem band_weight_source_negHigher (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (bandSourceWeight 0 0
      (fun j : Fin d ↦ if 1 ≤ j.val then -1 else 0)) u =
      -(fullHigherJetDegree u : ℤ) := by
  simp only [Finsupp.weight_eq_sum, fullHigherJetDegree, Fintype.sum_option,
    bandSourceWeight, nsmul_eq_mul, mul_zero, zero_add]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Fin.cases_zero, Fin.cases_succ]
  simp only [show ¬2 ≤ (0 : ℕ) by omega, ↓reduceIte, mul_zero, zero_add,
    Nat.cast_sum, Nat.cast_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : 1 ≤ j.val
  · have h' : 2 ≤ j.val + 1 := by omega
    simp [h, h']
  · have h' : ¬2 ≤ j.val + 1 := by omega
    simp [h, h']

private theorem band_weight_local_balance (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (bandLocalWeight (-1) 1 (fun _ : Fin d ↦ 0)) e =
      (e (localE d) : ℤ) - e (localT d) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, bandLocalWeight, localE, localAux, localT]
  ring

private theorem band_weight_local_higher (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (bandLocalWeight (-1) 1 (fun j : Fin d ↦ (j.val : ℤ))) e =
      (Finsupp.weight (localHigherJetWeight d) e : ℤ) + e (localE d) - e (localT d) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, bandLocalWeight,
    localHigherJetWeight, localE, localAux, localT, Nat.cast_sum, Nat.cast_mul]
  ring

private theorem band_weight_local_total (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (bandLocalWeight 0 1 (fun _ : Fin d ↦ 1)) e =
      (bandLocalJetDegree e : ℤ) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, bandLocalWeight,
    bandLocalJetDegree, Finsupp.degree_eq_sum, Nat.cast_sum]

private theorem band_weight_local_negHigher (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (bandLocalWeight 0 0
      (fun j : Fin d ↦ if 1 ≤ j.val then -1 else 0)) e =
      -(bandLocalHigherDegree e : ℤ) := by
  simp only [Finsupp.weight_eq_sum, bandLocalHigherDegree, Fintype.sum_option,
    bandLocalWeight, nsmul_eq_mul, mul_zero, zero_add, Nat.cast_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : 1 ≤ j.val <;> simp [h]

/-- Every unscaled local monomial has at least as many `T` factors as error factors.
This holds before contact projection and for every received point. -/
theorem band_unscaled_error_le_t (center received : R) (Q : DifferentialPolynomial R d)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    e (localE d) ≤ e (localT d) := by
  have h := unscaled_support_weight_le (-1) 1 0 0 (fun _ : Fin d ↦ 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun j ↦ by simp) center received (cap := 0)
    (fun u hu ↦ by
      simp [Finsupp.weight_eq_sum, bandSourceWeight, Fin.sum_univ_succ, Fintype.sum_option]) he
  rw [band_weight_local_balance] at h
  omega

/-- The retained higher-jet weight gains at most `i-h`, not merely `i`. -/
theorem band_unscaled_higher_weight_le (center received : R) {Q : DifferentialPolynomial R d}
    (hQ : ∀ u ∈ Q.support, fullHigherJetWeight u ≤ W)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    Finsupp.weight (localHigherJetWeight d) e ≤ W + (e (localT d) - e (localE d)) := by
  have h := unscaled_support_weight_le (-1) 1 0 0 (fun j : Fin d ↦ (j.val : ℤ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun j ↦ by simp) center received (cap := W)
    (fun u hu ↦ by rw [band_weight_source_higher]; exact_mod_cast hQ u hu) he
  rw [band_weight_local_higher] at h
  have hbalance := band_unscaled_error_le_t center received Q he
  omega

/-- The asymmetric lower degree edge survives the actual unscaled substitution. -/
theorem band_unscaled_higher_degree_ge (center received : R) {Q : DifferentialPolynomial R d}
    (hQ : ∀ u ∈ Q.support, Cmin ≤ fullHigherJetDegree u)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    Cmin ≤ bandLocalHigherDegree e := by
  have h := unscaled_support_weight_le 0 0 0 0
    (fun j : Fin d ↦ if 1 ≤ j.val then -1 else 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun j ↦ by split_ifs <;> norm_num) center received (cap := -(Cmin : ℤ))
    (fun u hu ↦ by
      rw [band_weight_source_negHigher]
      exact neg_le_neg (by exact_mod_cast hQ u hu)) he
  rw [band_weight_local_negHigher] at h
  omega

/-- A source total-jet degree cap is preserved by the actual local substitution. -/
theorem band_unscaled_jet_degree_le (center received : R) {Q : DifferentialPolynomial R d}
    {B : ℕ} (hQ : ∀ u ∈ Q.support, totalJetDegree u ≤ B)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    bandLocalJetDegree e ≤ B := by
  have h := unscaled_support_weight_le 0 1 0 1 (fun _ : Fin d ↦ 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun j ↦ by simp) center received (cap := B)
    (fun u hu ↦ by rw [band_weight_source_total]; exact_mod_cast hQ u hu) he
  rw [band_weight_local_total] at h
  exact_mod_cast h

/-- Strict total degree survives substitution, including nonpositive threshold edge cases. -/
theorem band_unscaled_jet_degree_lt (hD : 0 < D) (center received : R)
    {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ asymmetricBandSpace R D d m W Cmin Cmax L hD)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    (bandLocalJetDegree e : ℝ) < L / D := by
  have hsource : ∀ u ∈ Q.support, (totalJetDegree u : ℝ) < L / D :=
    fun u hu ↦ totalJetDegree_lt_of_asymmetricBandEligible hD
      (mem_asymmetricBandSpace_iff.mp hQ u hu)
  have hne : Q ≠ 0 := by
    intro hz
    simp [hz] at he
  obtain ⟨u, hu⟩ := (MvPolynomial.support_nonempty.mpr hne)
  have hpos : 0 < ⌈L / D⌉₊ :=
    (Nat.zero_le (totalJetDegree u)).trans_lt (Nat.lt_ceil.mpr (hsource u hu))
  have hbound := band_unscaled_jet_degree_le center received
    (B := ⌈L / D⌉₊ - 1)
    (fun u hu ↦ by have := Nat.lt_ceil.mpr (hsource u hu); omega) he
  apply Nat.lt_ceil.mp
  omega

private theorem band_mem_support_project {P : LocalPolynomial R d}
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (projectLowContact m P).support) :
    localContactOrder d e < m ∧ e ∈ P.support := by
  rw [MvPolynomial.mem_support_iff, projectLowContact, coeff_filterLocalMonomials] at he
  split_ifs at he with h
  · exact ⟨h, MvPolynomial.mem_support_iff.mpr he⟩
  · exact False.elim (he rfl)

/-- Actual local support satisfies all five inequalities of `band-reachable-coordinates`.
Here `bandLocalJetDegree` is `h+e+|z|`; no image or rank hypothesis is assumed. -/
theorem asymmetricBand_localConstraint_support (hD : 0 < D) (center received : R)
    {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ asymmetricBandSpace R D d m W Cmin Cmax L hD)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e (localE d) ≤ e (localT d) ∧
      Finsupp.weight (localHigherJetWeight d) e ≤ W + (e (localT d) - e (localE d)) ∧
      localContactOrder d e < m ∧ Cmin ≤ bandLocalHigherDegree e ∧
      (bandLocalJetDegree e : ℝ) < L / D := by
  have hp := band_mem_support_project he
  have hs := mem_asymmetricBandSpace_iff.mp hQ
  exact ⟨band_unscaled_error_le_t center received Q hp.2,
    band_unscaled_higher_weight_le center received (fun u hu ↦ (hs u hu).2.1) hp.2,
    hp.1,
    band_unscaled_higher_degree_ge center received (fun u hu ↦ (hs u hu).2.2.1) hp.2,
    band_unscaled_jet_degree_lt hD center received hQ hp.2⟩

private theorem bandLocalHigherDegree_eq_coordinates (hd : 0 < d)
    (e : LocalVariable d →₀ ℕ) :
    bandLocalHigherDegree e =
      higherJetTupleDegree (localExponentCoordinatesEquiv hd e).2.2.2 := by
  rw [bandLocalHigherDegree, Finsupp.weight_eq_sum, Fintype.sum_option, Fintype.sum_option]
  simp only [nsmul_eq_mul, mul_zero, zero_add]
  rw [sum_localJet_eq_first_add_higher hd]
  simp [higherJetTupleDegree, localY]

private theorem bandLocalJetDegree_eq_coordinates (hd : 0 < d)
    (e : LocalVariable d →₀ ℕ) :
    bandLocalJetDegree e = (localExponentCoordinatesEquiv hd e).2.1 +
      (localExponentCoordinatesEquiv hd e).2.2.1 +
      higherJetTupleDegree (localExponentCoordinatesEquiv hd e).2.2.2 := by
  rw [bandLocalJetDegree, Finsupp.degree_eq_sum, Fintype.sum_option,
    sum_localJet_eq_first_add_higher hd]
  simp [higherJetTupleDegree, localU, localAux, localY, Nat.add_assoc]

private theorem bandContact_eq_coordinates (hd : 0 < d) (e : LocalVariable d →₀ ℕ) :
    localContactOrder d e = (localExponentCoordinatesEquiv hd e).1 +
      d * (localExponentCoordinatesEquiv hd e).2.1 := by
  simp [localContactOrder, Finsupp.weight_eq_sum, Fintype.sum_option,
    localContactWeight, localT, localU, localAux, Nat.mul_comm]

/-- Decode a counted potential coordinate by setting `i = r+h`. -/
def asymmetricBandBudgetExponent (hd : 0 < d) {Be : ℕ}
    (p : AsymmetricBandLocalBudgetIndex d m W Be) : LocalVariable d →₀ ℕ :=
  (localExponentCoordinatesEquiv hd).symm
    (p.2.1.val + p.2.2.1.val, (p.2.2.1.val, (p.1.val, p.2.2.2.val)))

/-- Finite local support containing the actual image. The index may overcount this support. -/
def asymmetricBandLocalExponents (hd : 0 < d) (m W Be : ℕ) :
    Finset (LocalVariable d →₀ ℕ) :=
  Finset.univ.image (asymmetricBandBudgetExponent (m := m) (W := W) (Be := Be) hd)

/-- The potential local support has at most the manuscript's explicit budget many monomials. -/
theorem card_asymmetricBandLocalExponents_le (hd : 0 < d) (m W Be : ℕ) :
    (asymmetricBandLocalExponents hd m W Be).card ≤ asymmetricBandLocalBudget d m W Be := by
  exact Finset.card_image_le.trans (by
    rw [Finset.card_univ, card_asymmetricBandLocalBudgetIndex])

/-- Embed every actually retained coordinate into the finite `T`-sensitive budget support.
The error exponent uses denominator `d+1` after the change `r=i-h`. -/
theorem asymmetricBand_localConstraint_mem_exponents (hd : 0 < d) (hD : 0 < D)
    (center received : R) {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ asymmetricBandSpace R D d m W Cmin Cmax L hD)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e ∈ asymmetricBandLocalExponents hd m W ⌈L / D - Cmin⌉₊ := by
  obtain ⟨hbalance, hweight, hcontact, hlower, htotal⟩ :=
    asymmetricBand_localConstraint_support hD center received hQ he
  rw [bandLocalHigherDegree_eq_coordinates hd] at hlower
  rw [bandLocalJetDegree_eq_coordinates hd] at htotal
  rw [bandContact_eq_coordinates hd] at hcontact
  rw [localHigherJetWeight_eq_coordinate hd] at hweight
  let c := localExponentCoordinatesEquiv hd e
  have hb : c.2.1 ≤ c.1 := hbalance
  have hc : c.1 + d * c.2.1 < m := hcontact
  have hr : c.1 - c.2.1 < m := by omega
  have hh : c.2.1 < (m - (c.1 - c.2.1)) ⌈/⌉ (d + 1) := by
    apply lt_of_not_ge
    intro h
    have hmul := (ceilDiv_le_iff_le_mul (Nat.succ_pos d)).mp h
    rw [Nat.succ_mul] at hmul
    omega
  have hz : c.2.2.2 ∈ weightedHigherJetTuples d (W + (c.1 - c.2.1)) :=
    mem_weightedHigherJetTuples.mpr hweight
  have he₁ : c.2.2.1 < ⌈L / D - Cmin⌉₊ := by
    apply Nat.lt_ceil.mpr
    have hl : (Cmin : ℝ) ≤ higherJetTupleDegree c.2.2.2 := by exact_mod_cast hlower
    have ht : ((c.2.1 + c.2.2.1 + higherJetTupleDegree c.2.2.2 : ℕ) : ℝ) < L / D :=
      htotal
    push_cast at ht
    have hnonneg : (0 : ℝ) ≤ c.2.1 := Nat.cast_nonneg _
    linarith
  let p : AsymmetricBandLocalBudgetIndex d m W ⌈L / D - Cmin⌉₊ :=
    (⟨c.2.2.1, he₁⟩, ⟨⟨c.1 - c.2.1, hr⟩, (⟨c.2.1, hh⟩, ⟨c.2.2.2, hz⟩)⟩)
  apply Finset.mem_image.mpr
  refine ⟨p, Finset.mem_univ _, ?_⟩
  apply (localExponentCoordinatesEquiv hd).injective
  change (localExponentCoordinatesEquiv hd)
    ((localExponentCoordinatesEquiv hd).symm
      (c.1 - c.2.1 + c.2.1, (c.2.1, (c.2.2.1, c.2.2.2)))) = c
  simp [Nat.sub_add_cancel hb]

/-- The actual local map restricted to the asymmetric-band polynomial space. -/
def asymmetricBandLocalConstraint (hD : 0 < D) (center received : R) :
    asymmetricBandSpace R D d m W Cmin Cmax L hD →ₗ[R] LocalPolynomial R d :=
  (localConstraintAt m center received).domRestrict _

/-- Actual local rank is bounded by the explicit asymmetric-band coordinate count.
No characteristic assumption, nonempty-band hypothesis, or unproved rank premise is needed. -/
theorem finrank_asymmetricBandLocalConstraint_le {F : Type*} [Field F]
    (hd : 0 < d) (hD : 0 < D) (center received : F) :
    Module.finrank F (LinearMap.range
      (asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received)) ≤
      asymmetricBandLocalBudget d m W ⌈L / D - Cmin⌉₊ := by
  let s := asymmetricBandLocalExponents hd m W ⌈L / D - Cmin⌉₊
  let V := MvPolynomial.restrictSupport F (s : Set (LocalVariable d →₀ ℕ))
  let b := MvPolynomial.basisRestrictSupport (R := F) (s : Set (LocalVariable d →₀ ℕ))
  let _ : Module.Finite F V := Module.Finite.of_basis b
  have hdim : Module.finrank F V = s.card := by
    rw [← Fintype.card_coe]
    exact Module.finrank_eq_card_basis b
  have hsubset : LinearMap.range
      (asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received) ≤ V := by
    rintro _ ⟨Q, rfl⟩
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro e he
    exact asymmetricBand_localConstraint_mem_exponents hd hD center received Q.2 he
  exact (Submodule.finrank_mono hsubset).trans (hdim.le.trans
    (card_asymmetricBandLocalExponents_le hd m W ⌈L / D - Cmin⌉₊))

end ReedSolomon.HiddenDerivative
