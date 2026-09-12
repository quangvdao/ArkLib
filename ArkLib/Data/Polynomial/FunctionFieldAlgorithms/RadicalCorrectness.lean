/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.NormalizationArithmetic
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.NormalizationMultiplicity
public import Mathlib.RingTheory.Polynomial.Radical

/-!
# Correctness interface for saturated bivariate radicalization

This module records the semantic contract of the executable saturated radical producer.
The canonical specification is the unique-factorization radical after localization from
`F[X][Y]` to `F(X)[Y]`; the exported certificate also contains every global consequence
needed by the ordinary decoder.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.RadicalCorrectness

open CompPoly CPolynomial CPoly
open BivariateReducedSupport OrdinaryNormalization
open NormalizationArithmetic
open NormalizationMultiplicity
open UniqueFactorizationMonoid

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The stored outer degree agrees with the mathematical `Y` degree. -/
theorem stored_natDegree_eq (H : CBivariate F) :
    H.natDegree = (CBivariate.toPoly H).natDegree := by
  change H.natDegreeY = (CBivariate.toPoly H).natDegree
  exact (CBivariate.natDegreeY_toPoly H).symm

private theorem toPoly_ne_zero {H : CBivariate F} (hH : H ≠ 0) :
    CBivariate.toPoly H ≠ 0 := by
  let _ : DecidableEq F := instDecidableEqOfLawfulBEq
  intro hpoly
  apply hH
  apply CBivariate.ringEquiv.injective
  change CBivariate.toPoly H = CBivariate.toPoly 0
  simpa only [CBivariate.toPoly_zero] using hpoly

/-- Compact recursive invariant. The global decoder certificate is derived from this association
by Gauss descent and the input multiplicity bound. -/
structure LocalizedCertificate (input output : CBivariate F) : Prop where
  output_ne_zero : output ≠ 0
  output_isPrimitive : (CBivariate.toPoly output).IsPrimitive
  associated_radical : Associated (ClearDenominators.valueGlobal output)
    (localizedRadical input)

/-- The proof-only localized radical is squarefree. -/
theorem localizedRadical_squarefree (H : CBivariate F) : Squarefree (localizedRadical H) := by
  let _ : DecidableEq (RatFunc F) := Classical.decEq _
  unfold NormalizationMultiplicity.localizedRadical
  unfold NormalizationMultiplicity.polynomialRadical
  exact UniqueFactorizationMonoid.squarefree_radical

/-- The proof-only localized radical divides its source. -/
theorem localizedRadical_dvd (H : CBivariate F) :
    localizedRadical H ∣ ClearDenominators.valueGlobal H := by
  let _ : DecidableEq (RatFunc F) := Classical.decEq _
  unfold NormalizationMultiplicity.localizedRadical
  unfold NormalizationMultiplicity.polynomialRadical
  exact UniqueFactorizationMonoid.radical_dvd_self

/-- The global output of the compact recursive invariant is squarefree. -/
theorem LocalizedCertificate.output_squarefree {input output : CBivariate F}
    (cert : LocalizedCertificate input output) :
    Squarefree (CBivariate.toPoly output) := by
  apply squarefree_of_valueGlobal_squarefree cert.output_isPrimitive
  exact cert.associated_radical.squarefree_iff.mpr (localizedRadical_squarefree input)

/-- The compact recursive invariant already implies global output-to-input divisibility. -/
theorem LocalizedCertificate.output_dvd_input {input output : CBivariate F}
    (cert : LocalizedCertificate input output) :
    CBivariate.toPoly output ∣ CBivariate.toPoly input :=
  primitive_dvd_of_valueGlobal_associated cert.output_isPrimitive cert.associated_radical
    (localizedRadical_dvd input)

/-- Localization commutes with powers of stored global polynomials. -/
theorem valueGlobal_pow (H : CBivariate F) (n : ℕ) :
    ClearDenominators.valueGlobal (H ^ n) = ClearDenominators.valueGlobal H ^ n := by
  let _ : DecidableEq F := instDecidableEqOfLawfulBEq
  unfold ClearDenominators.valueGlobal
  rw [show CBivariate.toPoly (H ^ n) = CBivariate.toPoly H ^ n from
    map_pow CBivariate.ringEquiv H n, Polynomial.map_pow]

/-- Exact checked Frobenius contraction preserves the proof-only localized radical. -/
theorem localizedRadical_pow {p : ℕ} (hp : p ≠ 0) (root : CBivariate F) :
    localizedRadical (root ^ p) = localizedRadical root := by
  let _ : DecidableEq (RatFunc F) := Classical.decEq _
  unfold NormalizationMultiplicity.localizedRadical
  unfold NormalizationMultiplicity.polynomialRadical
  rw [NormalizationMultiplicity.localized_pow]
  exact UniqueFactorizationMonoid.radical_pow _ hp

/-- An exact returned joint root has the same localized radical as its powered residual. -/
theorem localizedRadical_jointRoot {p : ℕ} (hp : p ≠ 0) {inverse : F → F}
    {residual root : CBivariate F} (hroot : jointRoot p inverse residual = some root) :
    localizedRadical residual = localizedRadical root := by
  rw [← jointRoot_pow hroot, localizedRadical_pow hp]

/-- A nonzero primitive polynomial constant in `Y` localizes to a unit, so its radical is one. -/
theorem localizedRadical_eq_one_of_natDegree_eq_zero (H : CBivariate F)
    (hprimitive : (CBivariate.toPoly H).IsPrimitive)
    (hdegree : (CBivariate.toPoly H).natDegree = 0) : localizedRadical H = 1 := by
  let _ : DecidableEq F := instDecidableEqOfLawfulBEq
  let _ : DecidableEq (RatFunc F) := Classical.decEq _
  unfold NormalizationMultiplicity.localizedRadical
  unfold NormalizationMultiplicity.polynomialRadical
  apply UniqueFactorizationMonoid.radical_of_isUnit
  have heq : CBivariate.toPoly H = Polynomial.C ((CBivariate.toPoly H).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdegree
  have hunit : IsUnit ((CBivariate.toPoly H).coeff 0) :=
    hprimitive _ ⟨1, by simpa only [mul_one] using heq⟩
  unfold NormalizationMultiplicity.localized ClearDenominators.valueGlobal
  rw [heq, Polynomial.map_C]
  exact Polynomial.isUnit_C.mpr (hunit.map (algebraMap (Polynomial F) (RatFunc F)))

/-- Complete correctness contract for one output of saturated `Radical`.

The divisibility statements live in the global ring `F[X][Y]`; in particular, they retain
their meaning at fibers where a denominator-clearing scalar vanishes. -/
structure Certificate (ell : ℕ) (input output : CBivariate F) : Prop where
  /-- The returned support is not the zero polynomial. -/
  output_ne_zero : output ≠ 0
  /-- Executed denominator descent made the support primitive in `Y`. -/
  output_isPrimitive : (CBivariate.toPoly output).IsPrimitive
  /-- Every global irreducible factor occurs at most once. -/
  output_squarefree : Squarefree (CBivariate.toPoly output)
  /-- The reduced support is a global divisor of the input. -/
  output_dvd_input : CBivariate.toPoly output ∣ CBivariate.toPoly input
  /-- The bounded input multiplicities are covered by the `ell`-th support power. -/
  input_dvd_output_pow : CBivariate.toPoly input ∣ CBivariate.toPoly output ^ ell
  /-- The support and input define exactly the same polynomial graphs. -/
  graph_iff (P : Polynomial F) :
    (CBivariate.toPoly output).eval P = 0 ↔ (CBivariate.toPoly input).eval P = 0
  /-- Radicalization does not increase the outer `Y` degree. -/
  natDegree_le :
    (CBivariate.toPoly output).natDegree ≤ (CBivariate.toPoly input).natDegree
  /-- Radicalization does not increase the inner `X` degree. -/
  degreeX_le :
    Polynomial.Bivariate.degreeX (CBivariate.toPoly output) ≤
      Polynomial.Bivariate.degreeX (CBivariate.toPoly input)

/-- The two global divisibility conclusions imply graph equivalence over the base field. -/
theorem graph_iff_of_dvd {ell : ℕ} {input output : CBivariate F}
    (hell : ell ≠ 0) (hout : CBivariate.toPoly output ∣ CBivariate.toPoly input)
    (hin : CBivariate.toPoly input ∣ CBivariate.toPoly output ^ ell)
    (P : Polynomial F) :
    (CBivariate.toPoly output).eval P = 0 ↔ (CBivariate.toPoly input).eval P = 0 := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := hout
    rw [hq, Polynomial.eval_mul, h, MulZeroClass.zero_mul]
  · intro h
    obtain ⟨q, hq⟩ := hin
    have hp : ((CBivariate.toPoly output).eval P) ^ ell = 0 := by
      rw [← Polynomial.eval_pow, hq, Polynomial.eval_mul, h, MulZeroClass.zero_mul]
    exact (pow_eq_zero_iff hell).mp hp

/-- Package the semantic core of radical correctness into the complete consumer certificate. -/
theorem certificate_of_core {ell : ℕ} {input output : CBivariate F} (hell : ell ≠ 0)
    (houtput : output ≠ 0) (hprimitive : (CBivariate.toPoly output).IsPrimitive)
    (hsquarefree : Squarefree (CBivariate.toPoly output))
    (hout : CBivariate.toPoly output ∣ CBivariate.toPoly input)
    (hin : CBivariate.toPoly input ∣ CBivariate.toPoly output ^ ell) :
    Certificate ell input output := by
  classical
  have hinput : CBivariate.toPoly input ≠ 0 := by
    obtain ⟨q, hq⟩ := hin
    intro hz
    rw [hz, MulZeroClass.zero_mul] at hq
    have houtpoly : CBivariate.toPoly output ≠ 0 := by
      intro hzout
      apply houtput
      apply CBivariate.ringEquiv.injective
      change CBivariate.toPoly output = CBivariate.toPoly 0
      simpa only [CBivariate.toPoly_zero] using hzout
    exact pow_ne_zero ell houtpoly hq
  exact
    { output_ne_zero := houtput
      output_isPrimitive := hprimitive
      output_squarefree := hsquarefree
      output_dvd_input := hout
      input_dvd_output_pow := hin
      graph_iff := graph_iff_of_dvd hell hout hin
      natDegree_le := Polynomial.natDegree_le_of_dvd hout hinput
      degreeX_le := Polynomial.Bivariate.degreeX_le_of_dvd hout hinput }

/-- Convert the compact localization invariant into the global certificate consumed by decoding. -/
theorem certificate_of_localized {ell : ℕ} {input output : CBivariate F} (hell : ell ≠ 0)
    (hinput : input ≠ 0) (hinputPrimitive : (CBivariate.toPoly input).IsPrimitive)
    (hdegree : (CBivariate.toPoly input).natDegree ≤ ell)
    (cert : LocalizedCertificate input output) : Certificate ell input output := by
  have hlocalized : NormalizationMultiplicity.localized input ∣
      localizedRadical input ^ ell :=
    localized_dvd_localizedRadical_pow ell input hinput hdegree
  have hpower : Associated
      (NormalizationMultiplicity.localized output ^ ell) (localizedRadical input ^ ell) :=
    cert.associated_radical.pow_pow
  have hglobalPower : CBivariate.toPoly input ∣ CBivariate.toPoly output ^ ell :=
    primitive_dvd_pow_of_valueGlobal_dvd_pow hinputPrimitive
      (hlocalized.trans hpower.symm.dvd)
  exact certificate_of_core hell cert.output_ne_zero cert.output_isPrimitive
    cert.output_squarefree cert.output_dvd_input hglobalPower

end Polynomial.FunctionFieldAlgorithms.RadicalCorrectness

end

namespace Polynomial.FunctionFieldAlgorithms.RadicalCorrectness

open CompPoly CPolynomial CPoly
open BivariateReducedSupport OrdinaryNormalization
open NormalizationArithmetic NormalizationMultiplicity
open UniqueFactorizationMonoid

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

private theorem recursive_core_of_saturation (p ell : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : p ≤ ell → ∀ a, inverse a ^ p = a)
    (hsaturation : ∀ (H : CBivariate F) (step : Saturation F),
      H ≠ 0 → (CBivariate.toPoly H).IsPrimitive →
      (CBivariate.toPoly H).natDegree ≤ ell → saturate ell H = .ok step →
      SaturationCertificate p ell inverse H step)
    (H : CBivariate F) (hH : H ≠ 0) (hprimitive : (CBivariate.toPoly H).IsPrimitive)
    (hdegree : (CBivariate.toPoly H).natDegree ≤ ell) :
    ∃ output, radical p inverse ell H = .ok output ∧ LocalizedCertificate H output := by
  classical
  induction H using radical.induct p inverse ell with
  | case1 H hbound ih =>
      rw [stored_natDegree_eq] at hbound
      exact False.elim (Nat.not_lt_of_ge hdegree hbound)
  | case2 H hbound ih =>
      by_cases hzeroDegree : H.natDegree = 0
      · refine ⟨1, ?_, ?_⟩
        · rw [OrdinaryNormalization.radical.eq_def]
          have hcheck : (H.natDegree == 0) = true := beq_iff_eq.mpr hzeroDegree
          rw [if_neg hbound, if_pos hcheck]
          rfl
        · refine ⟨?_, ?_, ?_⟩
          · intro hone
            have honePoly := congrArg CBivariate.toPoly hone
            exact one_ne_zero (by simpa only [CBivariate.toPoly_one,
              CBivariate.toPoly_zero] using honePoly)
          · simpa only [CBivariate.toPoly_one] using
              (Polynomial.isPrimitive_one : (1 : Polynomial (Polynomial F)).IsPrimitive)
          have hlocalizedOne : ClearDenominators.valueGlobal (1 : CBivariate F) = 1 := by
            simpa only [pow_zero] using
              (NormalizationMultiplicity.localized_pow (1 : CBivariate F) 0)
          rw [hlocalizedOne,
            localizedRadical_eq_one_of_natDegree_eq_zero H hprimitive (by
              simpa only [← stored_natDegree_eq] using hzeroDegree)]
      · obtain ⟨step, hexec, _hv, _hr, _hvp, _hrp, _⟩ :=
          saturate_certificate ell hH
        have cert := hsaturation H step hH hprimitive hdegree hexec
        have hp := saturate_provenance ell H step hexec
        have hvprimitive : (CBivariate.toPoly step.visible).IsPrimitive :=
          quotientPrimitive_isPrimitive H step.common step.visible hp.2.1 cert.visible_ne_zero
        have hrprimitive : (CBivariate.toPoly step.residual).IsPrimitive :=
          quotientPrimitive_isPrimitive H step.removed step.residual hp.2.2.2 cert.residual_ne_zero
        by_cases hresDegree : step.residual.natDegree = 0
        · refine ⟨step.visible, ?_, ?_⟩
          · rw [OrdinaryNormalization.radical.eq_def]
            have hcheck : (H.natDegree == 0) = false :=
              beq_eq_false_iff_ne.mpr hzeroDegree
            have hresCheck : (step.residual.natDegree == 0) = true :=
              beq_iff_eq.mpr hresDegree
            rw [if_neg hbound]
            simp only [hcheck, Bool.false_eq_true, ↓reduceIte, hexec]
            change (if (step.residual.natDegree == 0) = true then
              Except.ok step.visible else _) = _
            rw [if_pos hresCheck]
          · refine ⟨cert.visible_ne_zero, hvprimitive, ?_⟩
            have hradResidual := localizedRadical_eq_one_of_natDegree_eq_zero
              step.residual hrprimitive (by
                simpa only [← stored_natDegree_eq] using hresDegree)
            have hsplit := cert.radical_split
            rw [hradResidual, mul_one] at hsplit
            exact hsplit.symm
        · have hrespos : 0 < step.residual.natDegree := Nat.pos_of_ne_zero hresDegree
          have hresposPoly : 0 < (CBivariate.toPoly step.residual).natDegree := by
            simpa only [← stored_natDegree_eq] using hrespos
          have hple : p ≤ ell := cert.p_le_ell_of_residual_nonconstant hresposPoly
          obtain ⟨root, hroot, hroot0, hrootPrimitive, hrootPow, hrootLt⟩ :=
            jointRoot_certificate p inverse (hinverse hple) cert.residual_ne_zero hrprimitive
              cert.residual_partials.1 cert.residual_partials.2 hrespos
          have hresDegreeLeH : step.residual.natDegree ≤ H.natDegree := by
            simpa only [stored_natDegree_eq] using
              (degree_bounds_of_dvd hH cert.outputs_dvd.2).1
          have hrootLtH : root.natDegree < H.natDegree := hrootLt.trans_le hresDegreeLeH
          have hrootDegree : (CBivariate.toPoly root).natDegree ≤ ell := by
            rw [← stored_natDegree_eq]
            exact (Nat.le_of_lt hrootLtH).trans (by
              simpa only [← stored_natDegree_eq] using hdegree)
          obtain ⟨recursive, hrecursive, ihcert⟩ :=
            ih root hrootLtH hroot0 hrootPrimitive hrootDegree
          refine ⟨step.visible * recursive, ?_, ?_⟩
          · rw [OrdinaryNormalization.radical.eq_def]
            have hcheck : (H.natDegree == 0) = false :=
              beq_eq_false_iff_ne.mpr hzeroDegree
            rw [if_neg hbound]
            simp only [hcheck, Bool.false_eq_true, ↓reduceIte, hexec]
            change (if (step.residual.natDegree == 0) = true then
              Except.ok step.visible else _) = _
            rw [if_neg (by simpa only [beq_iff_eq] using hresDegree)]
            rw [if_neg (Nat.not_lt_of_ge hple), hroot]
            simp only
            rw [dif_pos hrootLtH, hrecursive]
            rfl
          · refine ⟨?_, ?_, ?_⟩
            · intro hmul
              have hmulPoly := congrArg CBivariate.toPoly hmul
              exact mul_ne_zero (toPoly_ne_zero cert.visible_ne_zero)
                (toPoly_ne_zero ihcert.output_ne_zero) (by
                  simpa only [CBivariate.toPoly_mul, CBivariate.toPoly_zero] using hmulPoly)
            · simpa only [CBivariate.toPoly_mul] using
                hvprimitive.mul ihcert.output_isPrimitive
            have hresRadical : localizedRadical step.residual = localizedRadical root :=
              localizedRadical_jointRoot (Fact.out : Nat.Prime p).ne_zero hroot
            have hpieces : Associated
                (NormalizationMultiplicity.localized step.visible *
                  NormalizationMultiplicity.localized recursive)
                (NormalizationMultiplicity.localized step.visible *
                  localizedRadical step.residual) := by
              apply Associated.mul_left
              exact ihcert.associated_radical.trans (Associated.of_eq hresRadical.symm)
            rw [ClearDenominators.valueGlobal_mul]
            exact hpieces.trans cert.radical_split.symm

@[expose] public section

/-- The actual saturated radical call succeeds and returns a globally certified support.
All factor classification facts are derived from the executed saturation steps. -/
theorem radical_certificate (p ell : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : p ≤ ell → ∀ a, inverse a ^ p = a)
    (H : CBivariate F) (hH : H ≠ 0)
    (hprimitive : (CBivariate.toPoly H).IsPrimitive)
    (hdegree : (CBivariate.toPoly H).natDegree ≤ ell) (hell : ell ≠ 0) :
    ∃ output, radical p inverse ell H = .ok output ∧ Certificate ell H output := by
  obtain ⟨output, hexecution, hlocalized⟩ :=
    recursive_core_of_saturation p ell inverse hinverse
      (fun input step hinput hinputPrimitive hinputDegree hstep =>
        saturationCertificate p ell inverse input step hstep hinput
          hinputPrimitive hinputDegree hinverse)
      H hH hprimitive hdegree
  exact ⟨output, hexecution,
    certificate_of_localized hell hH hprimitive hdegree hlocalized⟩

end

end Polynomial.FunctionFieldAlgorithms.RadicalCorrectness
