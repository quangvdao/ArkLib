/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.OrdinaryNormalization

/-!
# Arithmetic completeness for ordinary normalization

This file complements the executable ordinary-normalization producer with converse arithmetic
bridges.  Global divisibility makes checked function-field division succeed, so both divisions in
the saturation stage are total on nonzero input.  It also packages the checked joint Frobenius
root with the nonzero, primitive, exact-power, and strict-degree facts used by radical recursion.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.NormalizationArithmetic

open CompPoly CPolynomial CPoly BivariateReducedSupport
open OrdinaryNormalization

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance : DecidableEq F := instDecidableEqOfLawfulBEq

private theorem valueGlobal_injective :
    Function.Injective (ClearDenominators.valueGlobal (F := F)) := by
  classical
  intro A B h
  apply CBivariate.ringEquiv.injective
  exact Polynomial.map_injective _ (RatFunc.algebraMap_injective F) h

private theorem valueGlobal_ne_zero {H : CBivariate F} (hH : H ≠ 0) :
    ClearDenominators.valueGlobal H ≠ 0 := by
  intro h
  apply hH
  apply valueGlobal_injective (F := F)
  simpa only [ClearDenominators.valueGlobal_zero] using h

/-- Removing the computed Y-content from a nonzero stored bivariate polynomial stays nonzero. -/
theorem primitivePart_ne_zero {H : CBivariate F} (hH : H ≠ 0) :
    ClearDenominators.primitivePart H ≠ 0 := by
  intro h
  apply hH
  rw [← ClearDenominators.content_mul_primitivePart H, h]
  simp

/-- The actual primitive-part producer satisfies Mathlib's coefficient-ring primitivity. -/
theorem primitivePart_isPrimitive {H : CBivariate F} (hH : H ≠ 0) :
    (CBivariate.toPoly (ClearDenominators.primitivePart H)).IsPrimitive :=
  (ClearDenominators.primitivePart_isYPrimitive hH).isPrimitive

private theorem toPoly_C (c : CPolynomial F) :
    CBivariate.toPoly (CPolynomial.C c : CBivariate F) = Polynomial.C c.toPoly := by
  classical
  rw [CBivariate.toPoly_eq_map, CPolynomial.C_toPoly, Polynomial.map_C]
  congr 1
  exact CPolynomial.ringEquiv_apply _

/-- The actual primitive part divides its source globally. -/
theorem primitivePart_dvd {H : CBivariate F} :
    CBivariate.toPoly (ClearDenominators.primitivePart H) ∣ CBivariate.toPoly H := by
  classical
  refine ⟨Polynomial.C (ClearDenominators.primitiveContent H).toPoly, ?_⟩
  have h := congrArg CBivariate.toPoly (ClearDenominators.content_mul_primitivePart H)
  rw [CBivariate.toPoly_mul] at h
  rw [toPoly_C] at h
  simpa only [mul_comm] using h.symm

/-- Content removal cannot increase the outer (Y) degree of a nonzero polynomial. -/
theorem primitivePart_natDegree_le {H : CBivariate F} (hH : H ≠ 0) :
    (CBivariate.toPoly (ClearDenominators.primitivePart H)).natDegree ≤
      (CBivariate.toPoly H).natDegree :=
  Polynomial.natDegree_le_of_dvd primitivePart_dvd <| by
    intro hz
    apply hH
    apply CBivariate.ringEquiv.injective
    change CBivariate.toPoly H = CBivariate.toPoly 0
    simpa only [CBivariate.toPoly_zero] using hz

/-- Content removal cannot increase the coefficient-variable (X) degree. -/
theorem primitivePart_degreeX_le {H : CBivariate F} (hH : H ≠ 0) :
    Polynomial.Bivariate.degreeX (CBivariate.toPoly (ClearDenominators.primitivePart H)) ≤
      Polynomial.Bivariate.degreeX (CBivariate.toPoly H) := by
  apply Polynomial.Bivariate.degreeX_le_of_dvd primitivePart_dvd
  intro hz
  apply hH
  apply CBivariate.ringEquiv.injective
  change CBivariate.toPoly H = CBivariate.toPoly 0
  simpa only [CBivariate.toPoly_zero] using hz

/-- Removing nonzero X-content preserves every polynomial graph equation. -/
theorem primitivePart_graph_iff {H : CBivariate F} (P : Polynomial F) :
    (CBivariate.toPoly (ClearDenominators.primitivePart H)).eval P = 0 ↔
      (CBivariate.toPoly H).eval P = 0 := by
  classical
  have h := congrArg (fun T : CBivariate F => (CBivariate.toPoly T).eval P)
    (ClearDenominators.content_mul_primitivePart H)
  rw [CBivariate.toPoly_mul, toPoly_C, Polynomial.eval_mul, Polynomial.eval_C] at h
  have hc := ClearDenominators.primitiveContent_ne_zero H
  constructor
  · intro hp
    rw [← h, hp, MulZeroClass.mul_zero]
  · intro hh
    rw [← h, mul_eq_zero] at hh
    exact hh.resolve_left hc

private theorem gcd_value_ne_zero (A B : CBivariate F) (hA : A ≠ 0) :
    FunctionFieldEuclid.value
      (FunctionFieldEuclid.gcd (ClearDenominators.embed A) (ClearDenominators.embed B)) ≠ 0 := by
  classical
  rw [FunctionFieldEuclid.value_gcd, ClearDenominators.value_embed,
    ClearDenominators.value_embed]
  intro hg
  have hd := EuclideanDomain.gcd_dvd_left
    (ClearDenominators.valueGlobal A) (ClearDenominators.valueGlobal B)
  rw [← normalize_dvd_iff, hg, zero_dvd_iff] at hd
  exact valueGlobal_ne_zero (F := F) hA hd

/-- The actual descended global gcd is nonzero when its left input is nonzero. -/
theorem globalGcd_ne_zero (A B : CBivariate F) (hA : A ≠ 0) :
    globalGcd A B ≠ 0 := by
  unfold globalGcd
  exact primitivePart_ne_zero
    (ClearDenominators.clear_global_ne_zero (gcd_value_ne_zero A B hA))

/-- The actual descended global gcd is primitive over `F[X]`. -/
theorem globalGcd_isPrimitive (A B : CBivariate F) (hA : A ≠ 0) :
    (CBivariate.toPoly (globalGcd A B)).IsPrimitive := by
  unfold globalGcd
  exact ClearDenominators.clear_primitive_isPrimitive (gcd_value_ne_zero A B hA)

/-- Global divisibility by a nonzero stored polynomial makes checked function-field division
succeed.  This is the completeness direction missing from the producer's soundness lemmas. -/
theorem quotientPrimitive_eq_some_of_dvd {A B : CBivariate F} (hB : B ≠ 0)
    (hBA : CBivariate.toPoly B ∣ CBivariate.toPoly A) :
    ∃ R, quotientPrimitive A B = some R := by
  classical
  obtain ⟨C, hC⟩ := hBA
  let Cstored : CBivariate F := CBivariate.ringEquiv.symm C
  have hCstored : CBivariate.toPoly Cstored = C :=
    CBivariate.ringEquiv.apply_symm_apply C
  have hdiv : FunctionFieldEuclid.divide (ClearDenominators.embed A)
      (ClearDenominators.embed B) = some (ClearDenominators.embed Cstored) := by
    rw [FunctionFieldEuclid.divide_eq_some_iff]
    constructor
    · intro hz
      apply hB
      apply valueGlobal_injective (F := F)
      rw [← ClearDenominators.value_embed, hz]
      simp [FunctionFieldEuclid.value, ClearDenominators.valueGlobal_zero,
        CPolynomial.toPoly_zero]
    · rw [ClearDenominators.value_embed, ClearDenominators.value_embed,
        ClearDenominators.value_embed]
      rw [ClearDenominators.valueGlobal, ClearDenominators.valueGlobal,
        ClearDenominators.valueGlobal, hCstored, hC, Polynomial.map_mul]
      ac_rfl
  refine ⟨ClearDenominators.primitivePart
    (ClearDenominators.descended (ClearDenominators.embed Cstored)), ?_⟩
  simp only [quotientPrimitive, hdiv, Option.map_some]

/-- A returned primitive quotient of a nonzero dividend is itself nonzero. -/
theorem quotientPrimitive_ne_zero {A B R : CBivariate F} (hA : A ≠ 0)
    (h : quotientPrimitive A B = some R) : R ≠ 0 := by
  unfold quotientPrimitive at h
  cases hq : FunctionFieldEuclid.divide (ClearDenominators.embed A)
      (ClearDenominators.embed B) with
  | none => simp [hq] at h
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at h
    subst R
    intro hzero
    change (ClearDenominators.clear q).primitive = 0 at hzero
    have hqzero : FunctionFieldEuclid.value q = 0 :=
      (ClearDenominators.clear_primitive_associated q).eq_zero_iff.mp <| by
        simpa only [ClearDenominators.valueGlobal_zero] using congrArg
          ClearDenominators.valueGlobal hzero
    have hprod := ((FunctionFieldEuclid.divide_eq_some_iff _ _ q).mp hq).2
    rw [hqzero, MulZeroClass.zero_mul] at hprod
    exact valueGlobal_ne_zero (F := F) hA <| by
      simpa only [ClearDenominators.value_embed] using hprod.symm

/-- Both exact quotients in the executable saturation stage succeed on nonzero input. -/
theorem saturate_eq_ok (ell : ℕ) {H : CBivariate F} (hH : H ≠ 0) :
    ∃ step, saturate ell H = .ok step := by
  classical
  let common := globalGcd H
    (globalGcd (CBivariate.partialDerivX H) (CBivariate.partialDerivY H))
  have hcommon : common ≠ 0 := globalGcd_ne_zero _ _ hH
  obtain ⟨visible, hvisible⟩ := quotientPrimitive_eq_some_of_dvd hcommon
    (globalGcd_dvd H _ hH).1
  have hremoved : globalGcd H (visible ^ ell) ≠ 0 := globalGcd_ne_zero _ _ hH
  obtain ⟨residual, hresidual⟩ := quotientPrimitive_eq_some_of_dvd hremoved
    (globalGcd_dvd H _ hH).1
  refine ⟨⟨common, visible, globalGcd H (visible ^ ell), residual⟩, ?_⟩
  unfold saturate
  dsimp only
  rw [show globalGcd H
    (globalGcd (CBivariate.partialDerivX H) (CBivariate.partialDerivY H)) = common from rfl]
  rw [hvisible]
  dsimp only
  rw [hresidual]
  rfl

/-- Successful saturation of nonzero input returns nonzero primitive visible and residual
quotients, each globally dividing the input and hence satisfying both axis-degree bounds. -/
theorem saturate_certificate (ell : ℕ) {H : CBivariate F} (hH : H ≠ 0) :
    ∃ step, saturate ell H = .ok step ∧ step.visible ≠ 0 ∧ step.residual ≠ 0 ∧
      (CBivariate.toPoly step.visible).IsPrimitive ∧
      (CBivariate.toPoly step.residual).IsPrimitive ∧
      CBivariate.toPoly step.visible ∣ CBivariate.toPoly H ∧
      CBivariate.toPoly step.residual ∣ CBivariate.toPoly H ∧
      (CBivariate.toPoly step.visible).natDegree ≤ (CBivariate.toPoly H).natDegree ∧
      (CBivariate.toPoly step.residual).natDegree ≤ (CBivariate.toPoly H).natDegree ∧
      Polynomial.Bivariate.degreeX (CBivariate.toPoly step.visible) ≤
        Polynomial.Bivariate.degreeX (CBivariate.toPoly H) ∧
      Polynomial.Bivariate.degreeX (CBivariate.toPoly step.residual) ≤
        Polynomial.Bivariate.degreeX (CBivariate.toPoly H) := by
  let common := globalGcd H
    (globalGcd (CBivariate.partialDerivX H) (CBivariate.partialDerivY H))
  have hcommon : common ≠ 0 := globalGcd_ne_zero _ _ hH
  obtain ⟨visible, hvisible⟩ := quotientPrimitive_eq_some_of_dvd hcommon
    (globalGcd_dvd H _ hH).1
  let removed := globalGcd H (visible ^ ell)
  have hremoved : removed ≠ 0 := globalGcd_ne_zero _ _ hH
  obtain ⟨residual, hresidual⟩ := quotientPrimitive_eq_some_of_dvd hremoved
    (globalGcd_dvd H _ hH).1
  let step : Saturation F := ⟨common, visible, removed, residual⟩
  have hs : saturate ell H = .ok step := by
    unfold saturate
    dsimp only
    rw [show globalGcd H
      (globalGcd (CBivariate.partialDerivX H) (CBivariate.partialDerivY H)) = common from rfl]
    rw [hvisible]
    dsimp only
    rw [show globalGcd H (visible ^ ell) = removed from rfl]
    rw [hresidual]
    rfl
  have hv : visible ≠ 0 := quotientPrimitive_ne_zero hH hvisible
  have hr : residual ≠ 0 := quotientPrimitive_ne_zero hH hresidual
  have hdv := quotientPrimitive_dvd_left_global _ _ _ hvisible hv
  have hdr := quotientPrimitive_dvd_left_global _ _ _ hresidual hr
  exact ⟨step, hs, hv, hr,
    quotientPrimitive_isPrimitive _ _ _ hvisible hv,
    quotientPrimitive_isPrimitive _ _ _ hresidual hr, hdv, hdr,
    quotientPrimitive_natDegree_le _ _ _ hvisible hH,
    quotientPrimitive_natDegree_le _ _ _ hresidual hH,
    quotientPrimitive_degreeX_le _ _ _ hvisible hH,
    quotientPrimitive_degreeX_le _ _ _ hresidual hH⟩

/-- Both zero partials and the inverse-Frobenius law produce an actual checked joint root.
The returned root is nonzero and primitive, has exact p-th power equal to the input, and strictly
decreases Y-degree whenever the input has positive Y-degree. -/
theorem jointRoot_certificate (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a) {Q : CBivariate F}
    (hQ : Q ≠ 0) (hprimitive : (CBivariate.toPoly Q).IsPrimitive)
    (hx : CBivariate.partialDerivX Q = 0) (hy : CBivariate.partialDerivY Q = 0)
    (hdegree : 0 < Q.natDegree) :
    ∃ R, jointRoot p inverse Q = some R ∧ R ≠ 0 ∧
      (CBivariate.toPoly R).IsPrimitive ∧ R ^ p = Q ∧ R.natDegree < Q.natDegree := by
  let R := jointContract p inverse Q
  have hroot : jointRoot p inverse Q = some R :=
    jointRoot_eq_some p inverse hinverse Q hx hy
  have hpow : R ^ p = Q := jointRoot_pow hroot
  have hR : R ≠ 0 := by
    intro hz
    apply hQ
    have := hpow
    rw [hz, zero_pow (Fact.out : Nat.Prime p).ne_zero] at this
    exact this.symm
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hpowPoly : CBivariate.toPoly R ^ p = CBivariate.toPoly Q := by
    calc
      CBivariate.toPoly R ^ p = CBivariate.toPoly (R ^ p) :=
        (map_pow CBivariate.ringEquiv R p).symm
      _ = CBivariate.toPoly Q := congrArg CBivariate.toPoly hpow
  have hdvd : CBivariate.toPoly R ∣ CBivariate.toPoly Q := by
    refine ⟨CBivariate.toPoly R ^ (p - 1), ?_⟩
    rw [← hpowPoly, ← pow_succ', Nat.sub_add_cancel hp]
  exact ⟨R, hroot, hR, Polynomial.isPrimitive_of_dvd hprimitive hdvd, hpow,
    jointRoot_degree_lt (Fact.out : Nat.Prime p).one_lt hroot hdegree⟩

/-- Global divisibility supplies the two original-relative degree bounds required by a radical
certificate. -/
theorem degree_bounds_of_dvd {S H : CBivariate F} (hH : H ≠ 0)
    (hdiv : CBivariate.toPoly S ∣ CBivariate.toPoly H) :
    (CBivariate.toPoly S).natDegree ≤ (CBivariate.toPoly H).natDegree ∧
      Polynomial.Bivariate.degreeX (CBivariate.toPoly S) ≤
        Polynomial.Bivariate.degreeX (CBivariate.toPoly H) := by
  have hpoly : CBivariate.toPoly H ≠ 0 := by
    intro h
    apply hH
    apply CBivariate.ringEquiv.injective
    change CBivariate.toPoly H = CBivariate.toPoly 0
    simpa only [CBivariate.toPoly_zero] using h
  exact ⟨Polynomial.natDegree_le_of_dvd hdiv hpoly,
    Polynomial.Bivariate.degreeX_le_of_dvd hdiv hpoly⟩

/-- Gauss descent for a general primitive global divisor, stated directly in the localization
used by the radical proof. -/
theorem primitive_dvd_of_valueGlobal_dvd {S H : CBivariate F}
    (hprimitive : (CBivariate.toPoly S).IsPrimitive)
    (hdiv : ClearDenominators.valueGlobal S ∣ ClearDenominators.valueGlobal H) :
    CBivariate.toPoly S ∣ CBivariate.toPoly H :=
  hprimitive.dvd_of_fraction_map_dvd_fraction_map hdiv

/-- A primitive polynomial associated to a localized radical divides the original globally. -/
theorem primitive_dvd_of_valueGlobal_associated {S H : CBivariate F}
    {localizedRadical : Polynomial (RatFunc F)}
    (hprimitive : (CBivariate.toPoly S).IsPrimitive)
    (hassociated : Associated (ClearDenominators.valueGlobal S) localizedRadical)
    (hdiv : localizedRadical ∣ ClearDenominators.valueGlobal H) :
    CBivariate.toPoly S ∣ CBivariate.toPoly H :=
  primitive_dvd_of_valueGlobal_dvd hprimitive (hassociated.dvd.trans hdiv)

/-- If a primitive input divides a power of the proposed support after localization, it already
divides that power in the global bivariate polynomial ring. -/
theorem primitive_dvd_pow_of_valueGlobal_dvd_pow {H S : CBivariate F} {ell : ℕ}
    (hprimitive : (CBivariate.toPoly H).IsPrimitive)
    (hdiv : ClearDenominators.valueGlobal H ∣ ClearDenominators.valueGlobal S ^ ell) :
    CBivariate.toPoly H ∣ CBivariate.toPoly S ^ ell := by
  apply hprimitive.dvd_of_fraction_map_dvd_fraction_map (K := RatFunc F)
  simpa only [ClearDenominators.valueGlobal, Polynomial.map_pow] using hdiv

/-- Squarefreeness over `F(X)` descends to a primitive polynomial over `F[X]`. -/
theorem squarefree_of_valueGlobal_squarefree {S : CBivariate F}
    (hprimitive : (CBivariate.toPoly S).IsPrimitive)
    (hsquarefree : Squarefree (ClearDenominators.valueGlobal S)) :
    Squarefree (CBivariate.toPoly S) := by
  classical
  intro d hdsq
  have hd : d ∣ CBivariate.toPoly S := (dvd_mul_right d d).trans hdsq
  have hdprimitive := Polynomial.isPrimitive_of_dvd hprimitive hd
  apply (hdprimitive.isUnit_iff_isUnit_map (K := RatFunc F)).mpr
  apply hsquarefree
  obtain ⟨q, hq⟩ := hdsq
  refine ⟨q.map (algebraMap (Polynomial F) (RatFunc F)), ?_⟩
  rw [ClearDenominators.valueGlobal, hq, Polynomial.map_mul, Polynomial.map_mul]

end Polynomial.FunctionFieldAlgorithms.NormalizationArithmetic
