/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.AsymmetricBandLocalRank
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Point independence of the asymmetric-band local rank

Translation in the global `X` and `Y₀` variables preserves the asymmetric band.  The local
constraint at an arbitrary point is therefore the zero-point constraint precomposed with a
linear automorphism of the band, so its actual rank is independent of the point.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R]
variable {d D m W Cmin Cmax : ℕ} {L : ℝ}

section MatrixBaseChange

/-- Extending the coefficient field cannot increase the rank of a finite matrix. -/
theorem Matrix.rank_map_algebraMap_le
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {ι κ : Type*} [Fintype κ]
    (A : Matrix ι κ F) :
    (A.map (algebraMap F E)).rank ≤ A.rank := by
  classical
  let p := Submodule.span F (Set.range A.col)
  let _ : Module.Finite F p := Module.Finite.span_of_finite F (Set.finite_range A.col)
  let b := Module.Free.chooseBasis F p
  let _ : Fintype (Module.Free.ChooseBasisIndex F p) := Fintype.ofFinite _
  let mapVec : (ι → F) →ₗ[F] (ι → E) :=
    LinearMap.pi fun i => (Algebra.linearMap F E).comp (LinearMap.proj i)
  let mapP : p →ₗ[F] (ι → E) := mapVec.comp p.subtype
  let v : Module.Free.ChooseBasisIndex F p → (ι → E) := fun q => mapP (b q)
  let _ : Module.Finite E (Submodule.span E (Set.range v)) :=
    Module.Finite.span_of_finite E (Set.finite_range v)
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  calc
    Module.finrank E (Submodule.span E (Set.range (A.map (algebraMap F E)).col))
        ≤ Module.finrank E (Submodule.span E (Set.range v)) := by
      apply Submodule.finrank_mono
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      have hcol : A.col j ∈ p := Submodule.subset_span (Set.mem_range_self j)
      have hmap : (A.map (algebraMap F E)).col j = mapVec (A.col j) := by
        ext i
        rfl
      rw [hmap]
      change mapP ⟨A.col j, hcol⟩ ∈ Submodule.span E (Set.range v)
      rw [← b.sum_repr ⟨A.col j, hcol⟩]
      simp only [map_sum, map_smul]
      apply Submodule.sum_mem
      intro q _
      rw [Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self q))
    _ ≤ Fintype.card (Module.Free.ChooseBasisIndex F p) := finrank_range_le_card v
    _ = Module.finrank F p := (Module.finrank_eq_card_basis b).symm

end MatrixBaseChange

section SupportWeights

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
variable {σ τ : Type*}

omit [PartialOrder M] [IsOrderedAddMonoid M] in
private theorem support_weight_C_eq_zero (w : τ → M) (a : R)
    {e : τ →₀ ℕ} (he : e ∈ (C a : MvPolynomial τ R).support) :
    Finsupp.weight w e = 0 := by
  classical
  have he' : e ∈ ({0} : Finset (τ →₀ ℕ)) := MvPolynomial.support_monomial_subset he
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

private theorem support_weight_mul_le (w : τ → M)
    {P Q : MvPolynomial τ R} {a b : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a)
    (hQ : ∀ e ∈ Q.support, Finsupp.weight w e ≤ b)
    {e : τ →₀ ℕ} (he : e ∈ (P * Q).support) :
    Finsupp.weight w e ≤ a + b := by
  classical
  obtain ⟨eP, heP, eQ, heQ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q he)
  simpa using add_le_add (hP eP heP) (hQ eQ heQ)

private theorem support_weight_pow_le (w : τ → M)
    {P : MvPolynomial τ R} {a : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a) (n : ℕ)
    {e : τ →₀ ℕ} (he : e ∈ (P ^ n).support) :
    Finsupp.weight w e ≤ n • a := by
  induction n generalizing e with
  | zero => simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | succ n ih =>
      rw [pow_succ] at he
      simpa [succ_nsmul] using support_weight_mul_le w (fun e he => ih he) hP he

private theorem support_weight_prod_le (w : τ → M)
    {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial τ R) (a : ι → M)
    (hP : ∀ i ∈ s, ∀ e ∈ (P i).support, Finsupp.weight w e ≤ a i)
    {e : τ →₀ ℕ} (he : e ∈ (s.prod P).support) :
    Finsupp.weight w e ≤ s.sum a := by
  classical
  induction s using Finset.induction_on generalizing e with
  | empty => simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi] at he
      rw [Finset.sum_insert hi]
      exact support_weight_mul_le w
        (hP i (Finset.mem_insert_self i s))
        (fun e he => ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)) he) he

private theorem support_weight_bind₁_le (wSource : σ → M) (wTarget : τ → M)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, ∀ e ∈ (f i).support, Finsupp.weight wTarget e ≤ wSource i)
    {P : MvPolynomial σ R} {a : M}
    (hP : ∀ u ∈ P.support, Finsupp.weight wSource u ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (MvPolynomial.bind₁ f P).support) :
    Finsupp.weight wTarget e ≤ a := by
  classical
  rw [MvPolynomial.as_sum P, map_sum] at he
  obtain ⟨u, hu, heu⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
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
    (fun v hv => le_of_eq (support_weight_C_eq_zero wTarget _ hv)) hprod heu
  have hmono : Finsupp.weight wTarget e ≤ Finsupp.weight wSource u := by
    simpa using hmul
  exact hmono.trans (hP u hu)

end SupportWeights

/-- Translate the two point coordinates in a differential polynomial. -/
def globalPointTranslation (center received : R) :
    DifferentialPolynomial R d →ₐ[R] DifferentialPolynomial R d :=
  bind₁ fun
    | none => C center + X none
    | some j => Fin.cases (C received + X (some 0)) (fun i => X (some i.succ)) j

@[simp] theorem globalPointTranslation_X (center received : R) :
    globalPointTranslation (d := d) center received (X none) = C center + X none := by
  simp [globalPointTranslation]

@[simp] theorem globalPointTranslation_Y_zero (center received : R) :
    globalPointTranslation (d := d) center received (X (some 0)) =
      C received + X (some 0) := by
  simp [globalPointTranslation]

@[simp] theorem globalPointTranslation_Y_succ (center received : R) (j : Fin d) :
    globalPointTranslation (d := d) center received (X (some j.succ)) = X (some j.succ) := by
  simp [globalPointTranslation]

private theorem globalPointTranslation_generator_weight_le
    {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    (w : JetVariable d → M) (hX : 0 ≤ w none) (hY₀ : 0 ≤ w (some 0))
    (center received : R) (v : JetVariable d) {e : JetVariable d →₀ ℕ}
    (he : e ∈ ((fun
      | none => C center + X none
      | some j => Fin.cases (C received + X (some 0))
          (fun i => X (some i.succ)) j) v : DifferentialPolynomial R d).support) :
    Finsupp.weight w e ≤ w v := by
  rcases v with _ | j
  · apply support_weight_add_le w ?_ ?_ he
    · intro u hu
      simpa [support_weight_C_eq_zero w _ hu] using hX
    · intro u hu
      exact (support_weight_X_eq w none hu).le
  · induction j using Fin.cases with
    | zero =>
      simp only [Fin.cases_zero] at he ⊢
      apply support_weight_add_le w ?_ ?_ he
      · intro u hu
        simpa [support_weight_C_eq_zero w _ hu] using hY₀
      · intro u hu
        exact (support_weight_X_eq w (some 0) hu).le
    | succ i =>
      simpa only [Fin.cases_succ] using (support_weight_X_eq w (some i.succ) he).le

private theorem globalPointTranslation_support_weight_le
    {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    (w : JetVariable d → M) (hX : 0 ≤ w none) (hY₀ : 0 ≤ w (some 0))
    (center received : R) {Q : DifferentialPolynomial R d} {a : M}
    (hQ : ∀ u ∈ Q.support, Finsupp.weight w u ≤ a)
    {e : JetVariable d →₀ ℕ} (he : e ∈ (globalPointTranslation center received Q).support) :
    Finsupp.weight w e ≤ a :=
  support_weight_bind₁_le w w _
    (globalPointTranslation_generator_weight_le w hX hY₀ center received) hQ he

private def bandFirstWeight : JetVariable d → ℕ
  | none => 0
  | some j => if j.val = 1 then 1 else 0

private def bandHigherWeight : JetVariable d → ℕ
  | none => 0
  | some j => j.val - 1

private def bandHigherDegreeWeight : JetVariable d → ℕ
  | none => 0
  | some j => if 2 ≤ j.val then 1 else 0

private def bandNegHigherDegreeWeight : JetVariable d → ℤ
  | none => 0
  | some j => if 2 ≤ j.val then -1 else 0

private def bandCoarseWeight (D : ℕ) : JetVariable d → ℕ
  | none => 1
  | some _ => D

private theorem weight_bandFirstWeight (u : JetVariable d →₀ ℕ) :
    Finsupp.weight bandFirstWeight u = firstJetExponent u := by
  simp [bandFirstWeight, firstJetExponent, Finsupp.weight_eq_sum, Fintype.sum_option]

private theorem weight_bandHigherWeight (u : JetVariable d →₀ ℕ) :
    Finsupp.weight bandHigherWeight u = fullHigherJetWeight u := by
  simp [bandHigherWeight, fullHigherJetWeight, Finsupp.weight_eq_sum, Fintype.sum_option]

private theorem weight_bandHigherDegreeWeight (u : JetVariable d →₀ ℕ) :
    Finsupp.weight bandHigherDegreeWeight u = fullHigherJetDegree u := by
  simp [bandHigherDegreeWeight, fullHigherJetDegree, Finsupp.weight_eq_sum,
    Fintype.sum_option]

private theorem weight_bandNegHigherDegreeWeight (u : JetVariable d →₀ ℕ) :
    Finsupp.weight bandNegHigherDegreeWeight u = -(fullHigherJetDegree u : ℤ) := by
  simp only [Finsupp.weight_eq_sum, Fintype.sum_option, bandNegHigherDegreeWeight,
    nsmul_eq_mul, mul_zero, zero_add, fullHigherJetDegree, Nat.cast_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : 2 ≤ j.val <;> simp [h]

private theorem weight_bandCoarseWeight (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (bandCoarseWeight D) u = u none + D * totalJetDegree u := by
  simp [bandCoarseWeight, Finsupp.weight_eq_sum, Fintype.sum_option,
    totalJetDegree, Finsupp.degree_eq_sum, Finset.mul_sum, mul_comm]

/-- Point translation preserves every defining inequality of the asymmetric band. -/
theorem globalPointTranslation_mem_asymmetricBandSpace (hD : 0 < D)
    (center received : R) {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ asymmetricBandSpace R D d m W Cmin Cmax L hD) :
    globalPointTranslation center received Q ∈
      asymmetricBandSpace R D d m W Cmin Cmax L hD := by
  rw [mem_asymmetricBandSpace_iff] at hQ ⊢
  intro e he
  have hfirst := globalPointTranslation_support_weight_le bandFirstWeight
    (by simp [bandFirstWeight]) (by simp [bandFirstWeight]) center received
    (a := m) (fun u hu => by rw [weight_bandFirstWeight]; exact (hQ u hu).1) he
  have hhigher := globalPointTranslation_support_weight_le bandHigherWeight
    (by simp [bandHigherWeight]) (by simp [bandHigherWeight]) center received
    (a := W) (fun u hu => by rw [weight_bandHigherWeight]; exact (hQ u hu).2.1) he
  have hdegreeLower := globalPointTranslation_support_weight_le bandNegHigherDegreeWeight
    (by simp [bandNegHigherDegreeWeight]) (by simp [bandNegHigherDegreeWeight]) center received
    (a := -(Cmin : ℤ)) (fun u hu => by
      rw [weight_bandNegHigherDegreeWeight]
      exact neg_le_neg (by exact_mod_cast (hQ u hu).2.2.1)) he
  have hdegreeUpper := globalPointTranslation_support_weight_le bandHigherDegreeWeight
    (by simp [bandHigherDegreeWeight]) (by simp [bandHigherDegreeWeight]) center received
    (a := Cmax) (fun u hu => by
      rw [weight_bandHigherDegreeWeight]
      exact (hQ u hu).2.2.2.1) he
  have hQne : Q ≠ 0 := by
    intro hzero
    simp [hzero] at he
  obtain ⟨u, hu⟩ := MvPolynomial.support_nonempty.mpr hQne
  have hceil : 0 < ⌈L⌉₊ := by
    have := (asymmetricBand_weight_lt_iff u).mp (hQ u hu).2.2.2.2
    omega
  have hcoarse := globalPointTranslation_support_weight_le (bandCoarseWeight D)
    (by simp [bandCoarseWeight]) (by simp [bandCoarseWeight]) center received
    (a := ⌈L⌉₊ - 1) (fun u hu => by
      rw [weight_bandCoarseWeight]
      have := (asymmetricBand_weight_lt_iff u).mp (hQ u hu).2.2.2.2
      omega) he
  rw [weight_bandFirstWeight] at hfirst
  rw [weight_bandHigherWeight] at hhigher
  rw [weight_bandNegHigherDegreeWeight] at hdegreeLower
  rw [weight_bandHigherDegreeWeight] at hdegreeUpper
  rw [weight_bandCoarseWeight] at hcoarse
  refine ⟨hfirst, hhigher, ?_, hdegreeUpper, ?_⟩
  · omega
  · rw [asymmetricBand_weight_lt_iff]
    omega

/-- Translation by opposite point coordinates is inverse to point translation. -/
theorem globalPointTranslation_neg_comp (center received : R) :
    (globalPointTranslation (d := d) (-center) (-received)).comp
      (globalPointTranslation center received) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with _ | j
  · simp
  · refine Fin.cases ?_ (fun i => ?_) j <;> simp

/-- Point translation restricts to a linear automorphism of the asymmetric band. -/
def asymmetricBandPointTranslation (hD : 0 < D) (center received : R) :
    asymmetricBandSpace R D d m W Cmin Cmax L hD ≃ₗ[R]
      asymmetricBandSpace R D d m W Cmin Cmax L hD where
  toFun Q := ⟨globalPointTranslation center received Q,
    globalPointTranslation_mem_asymmetricBandSpace hD center received Q.2⟩
  invFun Q := ⟨globalPointTranslation (-center) (-received) Q,
    globalPointTranslation_mem_asymmetricBandSpace hD (-center) (-received) Q.2⟩
  left_inv Q := by
    apply Subtype.ext
    exact AlgHom.congr_fun (globalPointTranslation_neg_comp center received) Q.1
  right_inv Q := by
    apply Subtype.ext
    simpa only [neg_neg, AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun (globalPointTranslation_neg_comp (-center) (-received)) Q.1
  map_add' Q P := by ext; simp
  map_smul' a Q := by ext; simp

/-- Local substitution at a point is zero-point substitution after global translation. -/
theorem unscaledLocalSubstitution_zero_comp_globalPointTranslation
    (center received : R) :
    (unscaledLocalSubstitution (R := R) d 0 0).comp
      (globalPointTranslation center received) =
        unscaledLocalSubstitution d center received := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with _ | j
  · simp
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp
      ring
    · simp

/-- The arbitrary-point local constraint is obtained from the zero-point map by translation. -/
theorem localConstraintAt_eq_zero_comp_globalPointTranslation
    (center received : R) (Q : DifferentialPolynomial R d) :
    localConstraintAt m center received Q =
      localConstraintAt m 0 0 (globalPointTranslation center received Q) := by
  unfold localConstraintAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [← AlgHom.comp_apply,
    unscaledLocalSubstitution_zero_comp_globalPointTranslation center received]

/-- Coordinate form of the actual local constraint restricted to the asymmetric band. -/
def asymmetricBandLocalCoordinateConstraint (hD : 0 < D) (center received : R) :
    asymmetricBandSpace R D d m W Cmin Cmax L hD →ₗ[R] (LowContactIndex d m → R) :=
  (localConstraintCoordinatesAt m center received).domRestrict _

/-- The coordinate-map rank is likewise independent of the point. -/
theorem finrank_range_asymmetricBandLocalCoordinateConstraint_eq_zero
    {F : Type*} [Field F] (hD : 0 < D) (center received : F) :
    Module.finrank F (LinearMap.range
      (asymmetricBandLocalCoordinateConstraint (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received)) =
      Module.finrank F (LinearMap.range
        (asymmetricBandLocalCoordinateConstraint (R := F) (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0)) := by
  let e := asymmetricBandPointTranslation (d := d) (m := m) (W := W)
    (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received
  have hmap : asymmetricBandLocalCoordinateConstraint (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received =
      (asymmetricBandLocalCoordinateConstraint (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0).comp e.toLinearMap := by
    apply LinearMap.ext
    intro Q
    ext row
    unfold asymmetricBandLocalCoordinateConstraint localConstraintCoordinatesAt
    simp only [LinearMap.domRestrict_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    change (lowContactCoefficients m)
        (unscaledLocalSubstitution d center received Q.1) row =
      (lowContactCoefficients m)
        (unscaledLocalSubstitution d 0 0
          (globalPointTranslation center received Q.1)) row
    rw [← AlgHom.comp_apply,
      unscaledLocalSubstitution_zero_comp_globalPointTranslation center received]
  rw [hmap, LinearMap.range_comp_of_range_eq_top _ e.range]

/-- Canonical infinite-row matrix of the actual asymmetric-band local coordinate map. -/
def asymmetricBandLocalCoordinateMatrix (hD : 0 < D) (center received : R) :
    Matrix (LowContactIndex d m)
      (AsymmetricBandIndex D d m W Cmin Cmax L hD) R :=
  fun row column =>
    localConstraintCoordinatesAt m center received
      (MvPolynomial.monomial column.1 1) row

/-- The monomial basis with its reducible band-space type made explicit. -/
def asymmetricBandTypedBasis (hD : 0 < D) :
    Module.Basis (AsymmetricBandIndex D d m W Cmin Cmax L hD) R
      (asymmetricBandSpace R D d m W Cmin Cmax L hD) :=
  asymmetricBandBasis (F := R) (d := d) (m := m) (W := W)
    (Cmin := Cmin) (Cmax := Cmax) (L := L) hD

private theorem asymmetricBandTypedBasis_apply (hD : 0 < D)
    (column : AsymmetricBandIndex D d m W Cmin Cmax L hD) :
    (asymmetricBandTypedBasis (R := R) (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD column :
        DifferentialPolynomial R d) = MvPolynomial.monomial column.1 1 := by
  unfold asymmetricBandTypedBasis asymmetricBandBasis
  change AddMonoidAlgebra.ofCoeff
      (↑((Finsupp.supportedEquivFinsupp
        (↑(asymmetricBandExponents D d m W Cmin Cmax L hD) :
          Set (JetVariable d →₀ ℕ))).symm (Finsupp.single column (1 : R)))) =
      MvPolynomial.monomial column.1 (1 : R)
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

@[simp] theorem asymmetricBandLocalCoordinateMatrix_apply (hD : 0 < D)
    (center received : R) (row : LowContactIndex d m)
    (column : AsymmetricBandIndex D d m W Cmin Cmax L hD) :
    asymmetricBandLocalCoordinateMatrix (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received row column =
      localConstraintCoordinatesAt m center received
        (MvPolynomial.monomial column.1 1) row := by
  rfl

/-- The canonical matrix rank is the actual coordinate-map range dimension. -/
theorem rank_asymmetricBandLocalCoordinateMatrix
    {F : Type*} [Field F] (hD : 0 < D) (center received : F) :
    (asymmetricBandLocalCoordinateMatrix (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received).rank =
      Module.finrank F (LinearMap.range
        (asymmetricBandLocalCoordinateConstraint (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received)) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  let b := asymmetricBandTypedBasis (R := F) (d := d) (m := m) (W := W)
    (Cmin := Cmin) (Cmax := Cmax) (L := L) hD
  let f := asymmetricBandLocalCoordinateConstraint (d := d) (m := m) (W := W)
    (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received
  have hrange : Submodule.span F
      (Set.range (asymmetricBandLocalCoordinateMatrix (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received).col) =
      LinearMap.range f := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨column, rfl⟩
      refine ⟨b column, ?_⟩
      ext row
      simp only [Matrix.col_apply, asymmetricBandLocalCoordinateMatrix]
      change f (b column) row = localConstraintCoordinatesAt m center received
          (MvPolynomial.monomial column.1 1) row
      unfold f asymmetricBandLocalCoordinateConstraint b
      simp only [LinearMap.domRestrict_apply]
      rw [asymmetricBandTypedBasis_apply]
    · rintro _ ⟨Q, rfl⟩
      rw [← b.sum_repr Q]
      simp only [map_sum, map_smul]
      apply Submodule.sum_mem
      intro column _
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨column, ?_⟩
      ext row
      simp only [Matrix.col_apply, asymmetricBandLocalCoordinateMatrix]
      change localConstraintCoordinatesAt m center received
          (MvPolynomial.monomial column.1 1) row = f (b column) row
      unfold f asymmetricBandLocalCoordinateConstraint b
      simp only [LinearMap.domRestrict_apply]
      rw [asymmetricBandTypedBasis_apply]
  rw [hrange]

/-- The canonical local matrix rank is point independent, even with its infinite row type. -/
theorem rank_asymmetricBandLocalCoordinateMatrix_eq_zero
    {F : Type*} [Field F] (hD : 0 < D) (center received : F) :
    (asymmetricBandLocalCoordinateMatrix (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received).rank =
      (asymmetricBandLocalCoordinateMatrix (d := d) (m := m) (W := W)
        (R := F) (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0).rank := by
  calc
    _ = Module.finrank F (LinearMap.range
        (asymmetricBandLocalCoordinateConstraint (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received)) :=
      rank_asymmetricBandLocalCoordinateMatrix hD center received
    _ = Module.finrank F (LinearMap.range
        (asymmetricBandLocalCoordinateConstraint (R := F) (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0)) :=
      finrank_range_asymmetricBandLocalCoordinateConstraint_eq_zero hD center received
    _ = _ := (rank_asymmetricBandLocalCoordinateMatrix hD (0 : F) 0).symm

/-- Coordinate extraction cannot have larger rank than the actual polynomial-valued local map. -/
theorem rank_asymmetricBandLocalCoordinateMatrix_le_actual
    {F : Type*} [Field F] (hD : 0 < D) (center received : F) :
    (asymmetricBandLocalCoordinateMatrix (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received).rank ≤
      Module.finrank F (LinearMap.range
        (asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received)) := by
  let _ : Module.Finite F (asymmetricBandSpace F D d m W Cmin Cmax L hD) :=
    Module.Finite.of_basis
      (asymmetricBandBasis (F := F) (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := L) hD)
  rw [rank_asymmetricBandLocalCoordinateMatrix]
  have hcomp : asymmetricBandLocalCoordinateConstraint (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received =
      (lowContactCoefficients (R := F) (d := d) m).comp
        (asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received) := by
    apply LinearMap.ext
    intro Q
    ext row
    simp [asymmetricBandLocalCoordinateConstraint, localConstraintCoordinatesAt,
      asymmetricBandLocalConstraint, localConstraintAt, lowContactCoefficients,
      projectLowContact, coeff_filterLocalMonomials, row.2]
  rw [hcomp, LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

private theorem map_unscaledLocalImage_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (v : JetVariable d) :
    MvPolynomial.map (algebraMap F E) (unscaledLocalImage d 0 0 v) =
      unscaledLocalImage d 0 0 v := by
  rcases v with _ | j
  · simp [unscaledLocalImage]
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp [unscaledLocalImage, localCorrection]
    · simp [unscaledLocalImage]

/-- Zero-point canonical entries commute with extension of the coefficient field. -/
theorem asymmetricBandLocalCoordinateMatrix_zero_baseChange
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (hD : 0 < D) :
    asymmetricBandLocalCoordinateMatrix (R := E) (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0 =
      (asymmetricBandLocalCoordinateMatrix (R := F) (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0).map (algebraMap F E) := by
  ext row column
  simp only [asymmetricBandLocalCoordinateMatrix_apply, Matrix.map_apply]
  unfold localConstraintCoordinatesAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, lowContactCoefficients,
    LinearMap.pi_apply, MvPolynomial.lcoeff_apply]
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp only [unscaledLocalSubstitution, MvPolynomial.bind₁_monomial,
    map_one, map_mul, map_prod, map_pow]
  simp_rw [map_unscaledLocalImage_zero]

/-- The arbitrary-point canonical matrix over an extension field is bounded by the source-field
zero-point matrix rank. -/
theorem rank_asymmetricBandLocalCoordinateMatrix_le_base
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (hD : 0 < D) (center received : E) :
    (asymmetricBandLocalCoordinateMatrix (R := E) (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received).rank ≤
      (asymmetricBandLocalCoordinateMatrix (R := F) (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0).rank := by
  rw [rank_asymmetricBandLocalCoordinateMatrix_eq_zero hD center received,
    asymmetricBandLocalCoordinateMatrix_zero_baseChange (F := F) (E := E) hD]
  exact Matrix.rank_map_algebraMap_le _

/-- Final local-rank seam: every extension-field point block is bounded by the source-field
actual zero-point asymmetric-band rank. -/
theorem rank_asymmetricBandLocalCoordinateMatrix_le_base_actual
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (hD : 0 < D) (center received : E) :
    (asymmetricBandLocalCoordinateMatrix (R := E) (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received).rank ≤
      Module.finrank F (LinearMap.range
        (asymmetricBandLocalConstraint (R := F) (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0)) :=
  (rank_asymmetricBandLocalCoordinateMatrix_le_base (F := F) hD center received).trans
    (rank_asymmetricBandLocalCoordinateMatrix_le_actual hD (0 : F) 0)

/-- The actual asymmetric-band local rank is independent of the center and received value. -/
theorem finrank_range_asymmetricBandLocalConstraint_eq_zero
    {F : Type*} [Field F] (hD : 0 < D) (center received : F) :
    Module.finrank F (LinearMap.range
      (asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received)) =
      Module.finrank F (LinearMap.range
        (asymmetricBandLocalConstraint (R := F) (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0)) := by
  let e := asymmetricBandPointTranslation (d := d) (m := m) (W := W)
    (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received
  have hmap : asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := L) hD center received =
      (asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := L) hD 0 0).comp e.toLinearMap := by
    apply LinearMap.ext
    intro Q
    exact localConstraintAt_eq_zero_comp_globalPointTranslation center received Q.1
  rw [hmap, LinearMap.range_comp_of_range_eq_top _ e.range]

end ReedSolomon.HiddenDerivative
