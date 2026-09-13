/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.OrdinaryFinalization

/-!
# Degree bounds for actual ordinary preparation

The supplied coordinate conversion respects both state-axis degrees. The actual cleared ordinary
message degree is at most `2 * (degreeZ + 1) * degreeY`, discharging finalization's internal
degree hypotheses under the paper cutoff. The final guard bound retains the actual canonical
denominator degrees and the cleared challenge degree explicitly; a bound for those quantities
in terms of the original challenge degree remains separate.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.OrdinaryDegreeBounds

open CompPoly CPolynomial CPoly

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance : DecidableEq F := instDecidableEqOfLawfulBEq

/-- Substituting constants in all but one variable cannot increase that axis degree. -/
theorem eval₂_axis_natDegree_le {R S : Type*} [CommSemiring R] [CommSemiring S]
    {n : ℕ} (q : MvPolynomial (Fin n) R) (g : R →+* S) (v : Fin n → S) (axis : Fin n) :
    (MvPolynomial.eval₂ (Polynomial.C.comp g)
      (fun i => if i = axis then Polynomial.X else Polynomial.C (v i)) q).natDegree ≤
        q.degreeOf axis := by
  classical
  rw [MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply Polynomial.natDegree_mul_le.trans
  simp only [RingHom.comp_apply, Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ i : Fin n, ((if i = axis then Polynomial.X else Polynomial.C (v i)) ^ m i).natDegree
        ≤ ∑ i : Fin n, if i = axis then m i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with h
      · exact Polynomial.natDegree_X_pow_le _
      · simp only [← Polynomial.C_pow, Polynomial.natDegree_C, le_refl]
    _ = m axis := by simp
    _ ≤ q.degreeOf axis := MvPolynomial.monomial_le_degreeOf axis hm

/-- The executed supplied equation has no larger derivative-state degree than its input. -/
theorem equation_natDegree_le (Q : CMvPolynomial 3 F) :
    (SuppliedInput.equation Q).natDegree ≤ Q.degreeOf 2 := by
  rw [RadicalCorrectness.stored_natDegree_eq, SuppliedInput.equation_toPoly]
  have h := eval₂_axis_natDegree_le (fromCMvPolynomial Q)
    (Polynomial.C.comp (SuppliedInput.constantHom (F := F)))
    ![Polynomial.C SuppliedInput.challenge, Polynomial.X, 0] 2
  have hv : (fun i : Fin 3 => if i = 2 then Polynomial.X else
      Polynomial.C (![Polynomial.C (SuppliedInput.challenge (F := F)), Polynomial.X, 0] i)) =
      SuppliedInput.stateVariables := by
    funext i
    fin_cases i <;> simp [SuppliedInput.stateVariables]
  rw [hv] at h
  simpa only [SuppliedInput.scalarHom, RingHom.comp_assoc,
    ← congrFun (degreeOf_equiv (S := F) (p := Q)) 2] using h

/-- The executed equation has no larger message degree than the supplied message axis. -/
theorem equation_degreeX_le (Q : CMvPolynomial 3 F) :
    Polynomial.Bivariate.degreeX (CBivariate.toPoly (SuppliedInput.equation Q)) ≤ Q.degreeOf 1 := by
  rw [← Polynomial.Bivariate.natDegreeY_swap]
  change (Polynomial.Bivariate.swap (CBivariate.toPoly (SuppliedInput.equation Q))).natDegree ≤ _
  rw [SuppliedInput.equation_toPoly]
  change ((Polynomial.Bivariate.swap (R := StoredField.Carrier F)).toRingHom
    (MvPolynomial.eval₂ SuppliedInput.scalarHom SuppliedInput.stateVariables
      (fromCMvPolynomial Q))).natDegree ≤ _
  rw [MvPolynomial.eval₂_comp_left]
  have h := eval₂_axis_natDegree_le (fromCMvPolynomial Q)
    (Polynomial.C.comp (SuppliedInput.constantHom (F := F)))
    ![Polynomial.C SuppliedInput.challenge, 0, Polynomial.X] 1
  have hv : (fun i : Fin 3 => if i = 1 then Polynomial.X else
      Polynomial.C (![Polynomial.C (SuppliedInput.challenge (F := F)), 0, Polynomial.X] i)) =
      (Polynomial.Bivariate.swap (R := StoredField.Carrier F)).toRingHom ∘
        SuppliedInput.stateVariables := by
    funext i
    change _ = Polynomial.Bivariate.swap (SuppliedInput.stateVariables i)
    fin_cases i <;> simp [SuppliedInput.stateVariables,
      Polynomial.Bivariate.swap_C_C, Polynomial.Bivariate.swap_X, Polynomial.Bivariate.swap_Y]
  have hg : (Polynomial.Bivariate.swap (R := StoredField.Carrier F)).toRingHom.comp
      SuppliedInput.scalarHom =
      Polynomial.C.comp (Polynomial.C.comp (SuppliedInput.constantHom (F := F))) := by
    ext a
    simp [SuppliedInput.scalarHom, Polynomial.Bivariate.swap_C_C]
  rw [hv] at h
  rw [hg]
  simpa only [← congrFun (degreeOf_equiv (S := F) (p := Q)) 1] using h

/-- Primitive content removal preserves the supplied derivative-state bound. -/
theorem primitive_equation_natDegree_le (Q : CMvPolynomial 3 F) (hQ : Q ≠ 0) :
    (ClearDenominators.primitivePart (SuppliedInput.equation Q)).natDegree ≤ Q.degreeOf 2 := by
  have h := NormalizationArithmetic.primitivePart_natDegree_le
    (SuppliedInput.equation_ne_zero hQ)
  rw [← RadicalCorrectness.stored_natDegree_eq, ← RadicalCorrectness.stored_natDegree_eq] at h
  exact h.trans (equation_natDegree_le Q)

/-- Clearing canonical coefficient denominators does not change the message degree. -/
theorem clear_global_natDegree (raw : CPolynomial (StoredField.Carrier F)) :
    (ClearDenominators.clear raw).global.natDegree = raw.natDegree := by
  have h := congrArg Polynomial.natDegree (ClearDenominators.clear_global_identity raw)
  have hs : algebraMap (Polynomial F) (RatFunc F)
      (ClearDenominators.clear raw).scale.toPoly ≠ 0 :=
    RatFunc.algebraMap_ne_zero (ClearDenominators.clear raw).scale_ne_zero
  simp only [ClearDenominators.valueGlobal, FunctionFieldEuclid.value,
    Polynomial.natDegree_map_eq_of_injective (RatFunc.algebraMap_injective F),
    Polynomial.natDegree_C_mul hs,
    Polynomial.natDegree_map_eq_of_injective (StoredField.valueHom (F := F)).injective] at h
  calc
    _ = (CBivariate.toPoly (ClearDenominators.clear raw).global).natDegree :=
      RadicalCorrectness.stored_natDegree_eq _
    _ = raw.toPoly.natDegree := h
    _ = raw.natDegree := (CPolynomial.natDegree_toPoly raw).symm

private theorem polynomial_ne_zero {H : CBivariate F} (hH : H ≠ 0) :
    CBivariate.toPoly H ≠ 0 := by
  intro h
  apply hH
  apply CBivariate.ringEquiv.injective
  change CBivariate.toPoly H = CBivariate.toPoly 0
  simpa only [CBivariate.toPoly_zero] using h

/-- The message-only content cannot exceed the original message degree. -/
theorem primitiveContent_natDegree_le (H : CBivariate F) (hH : H ≠ 0) :
    (ClearDenominators.primitiveContent H).natDegree ≤
      Polynomial.Bivariate.degreeX (CBivariate.toPoly H) := by
  have h := congrArg CBivariate.toPoly (ClearDenominators.content_mul_primitivePart H)
  rw [CBivariate.toPoly_mul, CBivariate.toPoly_eq_map, CPolynomial.C_toPoly,
    Polynomial.map_C] at h
  simp only [RingEquiv.coe_toRingHom, CPolynomial.ringEquiv_apply] at h
  change Polynomial.C (ClearDenominators.primitiveContent H).toPoly *
      CBivariate.toPoly (ClearDenominators.primitivePart H) = CBivariate.toPoly H at h
  have hd : (ClearDenominators.primitiveContent H).toPoly ∣
      (CBivariate.toPoly H).coeff (CBivariate.toPoly H).natDegree := by
    rw [← h, Polynomial.coeff_C_mul]
    exact dvd_mul_right _ _
  have hn : (CBivariate.toPoly H).coeff (CBivariate.toPoly H).natDegree ≠ 0 := by
    simpa only [Polynomial.coeff_natDegree] using
      Polynomial.leadingCoeff_ne_zero.mpr (polynomial_ne_zero hH)
  rw [CPolynomial.natDegree_toPoly]
  exact (Polynomial.natDegree_le_of_dvd hd hn).trans
    (Polynomial.Bivariate.coeff_natDegree_le_degreeX _ _)

/-- The actual resultant factor has the standard padded Sylvester message-degree bound. -/
theorem derivativeResultant_natDegree_le (H : CBivariate F) :
    (RegularCenterObstruction.derivativeResultant H).natDegree ≤
      2 * H.natDegree * Polynomial.Bivariate.degreeX (CBivariate.toPoly H) := by
  rw [CPolynomial.natDegree_toPoly,
    RegularCenterObstruction.derivativeResultant_toPoly_assignment_order,
    RadicalCorrectness.stored_natDegree_eq]
  exact (Polynomial.natDegree_resultant_derivative_padded_le _).trans
    (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

/-- Gcd, exact division, and the resultant bound the ordinary tail by the bidegrees of
its original equation whenever the executed support divides that equation. -/
theorem finish_ordinary_natDegree_le (original core support : CBivariate F)
    (ho : original ≠ 0) (hs : support ≠ 0)
    (hdvd : CBivariate.toPoly support ∣ CBivariate.toPoly original)
    (data : OrdinaryTail.Data F)
    (hr : OrdinaryTail.finish original core support = .prepared data) :
    data.ordinary.natDegree ≤
      2 * (original.natDegree + 1) * Polynomial.Bivariate.degreeX (CBivariate.toPoly original) := by
  classical
  unfold OrdinaryTail.finish at hr
  dsimp only at hr
  split at hr
  · cases hr
  · rename_i regular hq
    cases hr
    dsimp only
    let discarded := OrdinaryNormalization.globalGcd support (CBivariate.partialDerivY support)
    have hg := (OrdinaryNormalization.globalGcd_dvd support
      (CBivariate.partialDerivY support) hs).1
    have hdx := Polynomial.Bivariate.degreeX_le_of_dvd (hg.trans hdvd) (polynomial_ne_zero ho)
    have hcoeff : (CPolynomial.coeff discarded 0).natDegree ≤
        Polynomial.Bivariate.degreeX (CBivariate.toPoly original) := by
      rw [CPolynomial.natDegree_toPoly, ← CBivariate.toPoly_coeff]
      exact (Polynomial.Bivariate.coeff_natDegree_le_degreeX _ _).trans hdx
    have hsx := Polynomial.Bivariate.degreeX_le_of_dvd hdvd (polynomial_ne_zero ho)
    have hsd := Polynomial.natDegree_le_of_dvd hdvd (polynomial_ne_zero ho)
    have hrd := (OrdinaryNormalization.quotientPrimitive_natDegree_le _ _ _ hq hs).trans hsd
    have hrx := (OrdinaryNormalization.quotientPrimitive_degreeX_le _ _ _ hq hs).trans hsx
    rw [← RadicalCorrectness.stored_natDegree_eq,
      ← RadicalCorrectness.stored_natDegree_eq] at hrd
    have hlast : (if regular.natDegree == 0 then (1 : CPolynomial F) else
        RegularCenterObstruction.derivativeResultant regular).natDegree ≤
        2 * original.natDegree * Polynomial.Bivariate.degreeX (CBivariate.toPoly original) := by
      split
      · simp only [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_one, Polynomial.natDegree_one]
        exact Nat.zero_le _
      · exact (derivativeResultant_natDegree_le regular).trans
          (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hrd) hrx)
    have hmul (a b : CPolynomial F) : (a * b).natDegree ≤ a.natDegree + b.natDegree := by
      simp only [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul]
      exact Polynomial.natDegree_mul_le
    refine (hmul _ _).trans ((Nat.add_le_add (hmul _ _) hlast).trans ?_)
    have hc := primitiveContent_natDegree_le original ho
    change _ ≤ _ at hcoeff
    nlinarith

/-- The executed radical support gives a bidegree bound for the actual ordinary tail. -/
theorem run_ordinary_natDegree_le (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (equation : CBivariate F) (hequation : equation ≠ 0)
    (hdegree : (ClearDenominators.primitivePart equation).natDegree < p)
    (data : OrdinaryTail.Data F) (hrun : OrdinaryTail.run p inverse equation = .prepared data) :
    data.ordinary.natDegree ≤
      2 * (equation.natDegree + 1) * Polynomial.Bivariate.degreeX (CBivariate.toPoly equation) := by
  classical
  let core := ClearDenominators.primitivePart equation
  rw [OrdinaryTail.run, if_neg (by simpa using hequation)] at hrun
  dsimp only at hrun
  by_cases hd : core.natDegree = 0
  · rw [if_pos (by simpa [core] using hd)] at hrun
    apply finish_ordinary_natDegree_le equation core 1 hequation _ _ data hrun
    · intro hz
      have ht := congrArg CBivariate.toPoly hz
      simp [CBivariate.toPoly_one, CBivariate.toPoly_zero] at ht
    · simpa only [CBivariate.toPoly_one] using one_dvd (CBivariate.toPoly equation)
  · rw [if_neg (by simpa [core] using hd)] at hrun
    obtain ⟨support, hr, cert⟩ := RadicalCorrectness.radical_certificate p core.natDegree inverse
      (fun h => False.elim (Nat.not_le_of_gt hdegree h)) core
      (NormalizationArithmetic.primitivePart_ne_zero hequation)
      (NormalizationArithmetic.primitivePart_isPrimitive hequation)
      (by rw [← RadicalCorrectness.stored_natDegree_eq]) hd
    rw [show ClearDenominators.primitivePart equation = core from rfl, hr] at hrun
    exact finish_ordinary_natDegree_le equation core support hequation cert.output_ne_zero
      (cert.output_dvd_input.trans NormalizationArithmetic.primitivePart_dvd) data hrun

/-- The actual denominator-cleared ordinary equation is bounded solely by the two supplied
state-axis degrees; the challenge degree does not enter this message-degree bound. -/
theorem supplied_ordinary_natDegree_le (p : ℕ) [Fact p.Prime] [CharP F p]
    (Q : CMvPolynomial 3 F) (hQ : Q ≠ 0) (hd : Q.degreeOf 2 < p)
    (tail : OrdinaryTail.Data (StoredField.Carrier F))
    (hr : SuppliedInput.run p Q = .prepared tail) :
    (ClearDenominators.clear tail.ordinary).global.natDegree ≤
      2 * (Q.degreeOf 2 + 1) * Q.degreeOf 1 := by
  let : CharP (StoredField.Carrier F) p :=
    charP_of_injective_ringHom (SuppliedInput.constantHom (F := F)).injective p
  rw [clear_global_natDegree]
  have h := run_ordinary_natDegree_le p id (SuppliedInput.equation Q)
    (SuppliedInput.equation_ne_zero hQ) ((primitive_equation_natDegree_le Q hQ).trans_lt hd)
    tail hr
  exact h.trans (Nat.mul_le_mul
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (equation_natDegree_le Q) 1))
    (equation_degreeX_le Q))

/-- Actual finalization success under concrete supplied-axis bounds, with no computed-output
bound or successful-run witness supplied by the caller. -/
theorem run_exists_of_axes (p : ℕ) [Fact p.Prime] [CharP F p]
    (Q : CMvPolynomial 3 F) (hQ : Q ≠ 0) (hd : Q.degreeOf 2 < p)
    (ho : 2 * (Q.degreeOf 2 + 1) * Q.degreeOf 1 < p) :
    ∃ tail result, OrdinaryFinalization.run p id Q = some (tail, result) ∧ tail.ordinary ≠ 0 ∧
      OrdinaryNormalizationCorrectness.CorrectOutcome (OrdinaryFinalization.input tail.ordinary)
        result ∧ OrdinaryFinalization.guard tail.ordinary result ≠ 0 := by
  apply OrdinaryFinalization.run_exists p Q hQ ((primitive_equation_natDegree_le Q hQ).trans_lt hd)
  intro tail hr
  exact (supplied_ordinary_natDegree_le p Q hQ hd tail hr).trans_lt ho

omit [BEq F] [LawfulBEq F] in
/-- The paper's characteristic cutoff dominates both actual axis bounds. -/
theorem axis_bounds_of_kappa (Q : CMvPolynomial 3 F) (B p : ℕ)
    (hy : Q.degreeOf 1 ≤ B) (hz : Q.degreeOf 2 ≤ B)
    (hp : 2 * (B + 1) ^ 3 < p) :
    Q.degreeOf 2 < p ∧ 2 * (Q.degreeOf 2 + 1) * Q.degreeOf 1 < p := by
  have hpow : B + 1 ≤ (B + 1) ^ 3 := le_self_pow₀ (by omega) (by decide)
  have hb : B ≤ 2 * (B + 1) ^ 3 := by omega
  have hm : 2 * (Q.degreeOf 2 + 1) * Q.degreeOf 1 ≤ 2 * (B + 1) * B :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hz 1)) hy
  have hc : 2 * (B + 1) * B ≤ 2 * (B + 1) ^ 3 := by nlinarith
  exact ⟨(hz.trans hb).trans_lt hp, (hm.trans hc).trans_lt hp⟩

/-- Paper-shaped actual-run success under `p > kappa(B) = 2(B+1)^3`, with both state
axis degrees bounded by `B`. There is no Johnson or computed-output premise. -/
theorem run_exists_of_kappa (p : ℕ) [Fact p.Prime] [CharP F p]
    (Q : CMvPolynomial 3 F) (hQ : Q ≠ 0) (B : ℕ)
    (hy : Q.degreeOf 1 ≤ B) (hz : Q.degreeOf 2 ≤ B) (hp : 2 * (B + 1) ^ 3 < p) :
    ∃ tail result, OrdinaryFinalization.run p id Q = some (tail, result) ∧ tail.ordinary ≠ 0 ∧
      OrdinaryNormalizationCorrectness.CorrectOutcome (OrdinaryFinalization.input tail.ordinary)
        result ∧ OrdinaryFinalization.guard tail.ordinary result ≠ 0 := by
  obtain ⟨hd, ho⟩ := axis_bounds_of_kappa Q B p hy hz hp
  exact run_exists_of_axes p Q hQ hd ho

/-- Supplied-axis bounds also discharge the hypotheses of the complete final root partition. -/
theorem run_exists_partition_of_axes (p : ℕ) [Fact p.Prime] [CharP F p]
    (Q : CMvPolynomial 3 F) (hQ : Q ≠ 0) (hd : Q.degreeOf 2 < p)
    (ho : 2 * (Q.degreeOf 2 + 1) * Q.degreeOf 1 < p) :
    ∃ tail result, OrdinaryFinalization.run p id Q = some (tail, result) ∧
      OrdinaryNormalizationCorrectness.CorrectOutcome (OrdinaryFinalization.input tail.ordinary)
        result ∧ OrdinaryFinalization.guard tail.ordinary result ≠ 0 ∧
      ∀ P : Polynomial F,
        MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P, P.derivative]
          (fromCMvPolynomial Q) = 0 →
        OrdinaryFinalization.OrdinaryRoot result P ∨
          (RegularPart.evalAt StoredField.valueHom
            (algebraMap (Polynomial F) (RatFunc F) P)
            (algebraMap (Polynomial F) (RatFunc F) P.derivative) tail.regular = 0 ∧
           RegularPart.evalAt StoredField.valueHom
            (algebraMap (Polynomial F) (RatFunc F) P)
            (algebraMap (Polynomial F) (RatFunc F) P.derivative)
              (CBivariate.partialDerivY tail.regular) ≠ 0) := by
  apply OrdinaryFinalization.run_exists_partition p Q hQ
    ((primitive_equation_natDegree_le Q hQ).trans_lt hd)
  intro tail hr
  exact (supplied_ordinary_natDegree_le p Q hQ hd tail hr).trans_lt ho

/-- The actual clearing scale is bounded by the sum of the canonical denominator degrees. -/
theorem clearing_scale_natDegree_le (raw : CPolynomial (StoredField.Carrier F)) :
    (ClearDenominators.clear raw).scale.natDegree ≤
      ∑ i ∈ Finset.range raw.val.size, (StoredField.denominator (raw.coeff i)).natDegree := by
  change (ClearDenominators.denominatorProduct raw).natDegree ≤ _
  rw [CPolynomial.natDegree_toPoly]
  rw [ClearDenominators.denominatorProduct, ← CPolynomial.toPolyRingHom_apply, map_prod]
  simpa only [CPolynomial.toPolyRingHom_apply, CPolynomial.natDegree_toPoly] using
    Polynomial.natDegree_prod_le (Finset.range raw.val.size)
      (fun i => (StoredField.denominator (raw.coeff i)).toPoly)

/-- An actual normalized guard is bounded by the clearing scale and the output bidegrees. -/
theorem guard_natDegree_le (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F))
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree →
      ∀ a, inverse a ^ p = a) (data : OrdinaryNormalization.Data F)
    (hr : OrdinaryFinalization.finalize p inverse raw = .normalized data) :
    (OrdinaryFinalization.guard raw (.normalized data)).natDegree ≤
      (ClearDenominators.clear raw).scale.natDegree +
        2 * data.regular.natDegree *
          Polynomial.Bivariate.degreeX (CBivariate.toPoly data.regular) := by
  have hc := OrdinaryFinalization.finalize_correct p inverse raw hinverse
  rw [hr] at hc
  have hm : ((ClearDenominators.clear raw).scale.toPoly * data.obstruction.toPoly).natDegree ≤
      (ClearDenominators.clear raw).scale.toPoly.natDegree + data.obstruction.toPoly.natDegree :=
    Polynomial.natDegree_mul_le
  have ho := hc.obstruction_natDegree_le
  simp only [CPolynomial.natDegree_toPoly] at ho ⊢
  apply le_trans (by simpa only [OrdinaryFinalization.guard, CPolynomial.toPoly_mul] using hm)
  exact
    (Nat.add_le_add_left ho _)

/-- The normalized guard is bounded using only the raw ordinary coefficients and their
actual global descent; no degree of a caller-supplied normalized output appears on the right. -/
theorem guard_input_natDegree_le (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F))
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree →
      ∀ a, inverse a ^ p = a) (data : OrdinaryNormalization.Data F)
    (hr : OrdinaryFinalization.finalize p inverse raw = .normalized data) :
    (OrdinaryFinalization.guard raw (.normalized data)).natDegree ≤
      (∑ i ∈ Finset.range raw.val.size, (StoredField.denominator (raw.coeff i)).natDegree) +
        2 * raw.natDegree *
          Polynomial.Bivariate.degreeX
            (CBivariate.toPoly (ClearDenominators.clear raw).global) := by
  have hc := OrdinaryFinalization.finalize_correct p inverse raw hinverse
  rw [hr] at hc
  have hd := hc.natDegree_le_original
  have hx := hc.degreeX_le_original
  rw [hc.original_eq, OrdinaryFinalization.input_eq,
    ← RadicalCorrectness.stored_natDegree_eq, ← RadicalCorrectness.stored_natDegree_eq,
    clear_global_natDegree] at hd
  rw [hc.original_eq, OrdinaryFinalization.input_eq] at hx
  exact (guard_natDegree_le p inverse raw hinverse data hr).trans
    (Nat.add_le_add (clearing_scale_natDegree_le raw)
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hd) hx))

/-- Both successful branches obey the explicit input bound on the actual executed guard. -/
theorem final_guard_input_natDegree_le (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F)) (hraw : raw ≠ 0)
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree →
      ∀ a, inverse a ^ p = a) :
    (OrdinaryFinalization.guard raw (OrdinaryFinalization.finalize p inverse raw)).natDegree ≤
      (∑ i ∈ Finset.range raw.val.size, (StoredField.denominator (raw.coeff i)).natDegree) +
        2 * raw.natDegree *
          Polynomial.Bivariate.degreeX
            (CBivariate.toPoly (ClearDenominators.clear raw).global) := by
  rcases OrdinaryFinalization.finalize_nonzero p inverse raw hraw hinverse with
    ⟨data, hr, _⟩ | ⟨data, hr, _⟩
  · simp only [hr, OrdinaryFinalization.guard, CPolynomial.mul_one]
    exact (clearing_scale_natDegree_le raw).trans (Nat.le_add_right _ _)
  · rw [hr]
    exact guard_input_natDegree_le p inverse raw hinverse data hr

end Polynomial.FunctionFieldAlgorithms.CommonCenter.OrdinaryDegreeBounds
