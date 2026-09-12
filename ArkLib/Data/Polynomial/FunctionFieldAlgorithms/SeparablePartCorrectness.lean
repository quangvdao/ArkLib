/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.OrdinaryNormalization
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Correctness of the separable part of ordinary normalization

Starting from a nonzero primitive globally squarefree support, this file proves that the actual
function-field gcd and primitive quotient retain precisely the Y-separable part.  The discarded
factor has zero Y derivative and no polynomial graph, while the retained factor is primitive,
nonzero, and separable over `F(X)`.  These facts discharge every check in `finish`.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.SeparablePartCorrectness

open CompPoly CPolynomial CPoly BivariateReducedSupport
open OrdinaryNormalization
open scoped nonZeroDivisors Polynomial

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

private theorem toPoly_ne_zero {H : CBivariate F} (hH : H ≠ 0) :
    CBivariate.toPoly H ≠ 0 := by
  intro hzero
  apply hH
  calc
    H = CBivariate.ofPoly (CBivariate.toPoly H) := (CBivariate.toPoly_ofPoly H).symm
    _ = CBivariate.ofPoly 0 := congrArg CBivariate.ofPoly hzero
    _ = 0 := CBivariate.ofPoly_zero

private theorem globalGcd_ne_zero (A B : CBivariate F) (hA : A ≠ 0) :
    globalGcd A B ≠ 0 := by
  classical
  let g := FunctionFieldEuclid.gcd (ClearDenominators.embed A)
    (ClearDenominators.embed B)
  have hg : FunctionFieldEuclid.value g ≠ 0 := by
    rw [FunctionFieldEuclid.value_gcd, ClearDenominators.value_embed,
      ClearDenominators.value_embed]
    intro hz
    have hd := EuclideanDomain.gcd_dvd_left
      (ClearDenominators.valueGlobal A) (ClearDenominators.valueGlobal B)
    rw [← normalize_dvd_iff, hz, zero_dvd_iff] at hd
    exact valueGlobal_ne_zero (F := F) hA hd
  unfold globalGcd
  intro hz
  change (ClearDenominators.clear g).primitive = 0 at hz
  have hv : ClearDenominators.valueGlobal (ClearDenominators.clear g).primitive = 0 := by
    simpa only [ClearDenominators.valueGlobal_zero] using congrArg
      ClearDenominators.valueGlobal hz
  exact hg ((ClearDenominators.clear_primitive_associated g).eq_zero_iff.mp hv)

private theorem quotientPrimitive_eq_some_of_dvd {A B : CBivariate F} (hB : B ≠ 0)
    (hBA : CBivariate.toPoly B ∣ CBivariate.toPoly A) :
    ∃ R, quotientPrimitive A B = some R := by
  classical
  obtain ⟨C, hC⟩ := hBA
  let Cstored : CBivariate F := CBivariate.ringEquiv.symm C
  have hCstored : CBivariate.toPoly Cstored = C := CBivariate.ringEquiv.apply_symm_apply C
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

/-- A primitive squarefree polynomial remains squarefree after extending its coefficient GCD
domain to its fraction field. -/
theorem squarefree_valueGlobal {S : CBivariate F}
    (hprimitive : (CBivariate.toPoly S).IsPrimitive)
    (hsquarefree : Squarefree (CBivariate.toPoly S)) :
    Squarefree (ClearDenominators.valueGlobal S) := by
  classical
  change Squarefree ((CBivariate.toPoly S).map
    (algebraMap (Polynomial F) (RatFunc F)))
  intro d hdsq
  by_cases hdzero : d = 0
  · subst d
    exfalso
    have hmapzero : (CBivariate.toPoly S).map
        (algebraMap (Polynomial F) (RatFunc F)) = 0 := by
      simpa only [MulZeroClass.zero_mul, zero_dvd_iff] using hdsq
    exact (Polynomial.map_ne_zero_iff (RatFunc.algebraMap_injective F)).mpr
      hprimitive.ne_zero hmapzero
  let A : Polynomial (Polynomial F) :=
    IsLocalization.integerNormalization (Polynomial F)⁰ d
  let P : Polynomial (Polynomial F) := A.primPart
  obtain ⟨c, hc, hAmap⟩ :=
    IsLocalization.integerNormalization_spec (Polynomial F)⁰ d
  rw [Algebra.smul_def] at hAmap
  have hscalar : algebraMap (Polynomial F) (Polynomial (RatFunc F)) c =
      Polynomial.C (algebraMap (Polynomial F) (RatFunc F) c) := by
    rw [IsScalarTower.algebraMap_apply (Polynomial F) (RatFunc F)
      (Polynomial (RatFunc F))]
    rfl
  rw [hscalar] at hAmap
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hCunit : IsUnit
      (Polynomial.C (algebraMap (Polynomial F) (RatFunc F) c)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      (RatFunc.algebraMap_ne_zero hc0))
  have hA : A ≠ 0 := by
    intro hz
    change A.map (algebraMap (Polynomial F) (RatFunc F)) =
      Polynomial.C (algebraMap (Polynomial F) (RatFunc F) c) * d at hAmap
    rw [hz, Polynomial.map_zero] at hAmap
    exact hdzero (mul_eq_zero.mp hAmap.symm |>.resolve_left
      (Polynomial.C_ne_zero.mpr (RatFunc.algebraMap_ne_zero hc0)))
  have hcontent : A.content ≠ 0 := Polynomial.content_eq_zero_iff.not.mpr hA
  have hcontentUnit : IsUnit
      (Polynomial.C (algebraMap (Polynomial F) (RatFunc F) A.content)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      (RatFunc.algebraMap_ne_zero hcontent))
  have hPA : Associated
      (P.map (algebraMap (Polynomial F) (RatFunc F)))
      (A.map (algebraMap (Polynomial F) (RatFunc F))) := by
    have heq := congrArg
      (Polynomial.map (algebraMap (Polynomial F) (RatFunc F)))
      A.eq_C_content_mul_primPart
    rw [Polynomial.map_mul, Polynomial.map_C] at heq
    exact (associated_unit_mul_left _ _ hcontentUnit).symm.trans (Associated.of_eq heq.symm)
  have hAd : Associated (A.map (algebraMap (Polynomial F) (RatFunc F))) d := by
    exact (Associated.of_eq hAmap).trans (associated_unit_mul_left d _ hCunit)
  have hPd : Associated (P.map (algebraMap (Polynomial F) (RatFunc F))) d := hPA.trans hAd
  have hPPmap : (P * P).map (algebraMap (Polynomial F) (RatFunc F)) ∣
      (CBivariate.toPoly S).map (algebraMap (Polynomial F) (RatFunc F)) := by
    rw [Polynomial.map_mul]
    exact (hPd.mul_mul hPd).dvd.trans hdsq
  have hPP : P * P ∣ CBivariate.toPoly S :=
    (Polynomial.isPrimitive_primPart A).mul (Polynomial.isPrimitive_primPart A)
      |>.dvd_of_fraction_map_dvd_fraction_map hPPmap
  have hPunit : IsUnit P := hsquarefree P hPP
  exact hPd.isUnit (hPunit.map
    (Polynomial.mapRingHom (algebraMap (Polynomial F) (RatFunc F))))

/-- Dividing a nonzero polynomial over a field by a divisor associated to its derivative gcd
leaves a squarefree quotient. -/
private theorem squarefree_quotient_gcd_derivative {K : Type*} [Field K] [DecidableEq K]
    {H D Q : Polynomial K} (hH : H ≠ 0)
    (hassociated : Associated D (EuclideanDomain.gcd H H.derivative))
    (hfactor : Q * D = H) : Squarefree Q := by
  let radical := UniqueFactorizationMonoid.radical H
  let repeated := EuclideanDomain.divRadical H
  have hrepeatedDvdGCD : repeated ∣ EuclideanDomain.gcd H H.derivative := by
    apply EuclideanDomain.dvd_gcd
    · exact EuclideanDomain.divRadical_dvd_self H
    · change EuclideanDomain.divRadical H ∣ H.derivative
      exact divRadical_dvd_derivative H
  have hrepeatedDvdD : repeated ∣ D :=
    hassociated.dvd_iff_dvd_right.mpr hrepeatedDvdGCD
  obtain ⟨multiplier, hmultiplier⟩ := hrepeatedDvdD
  have hcancel : repeated * (multiplier * Q) = repeated * radical := by
    calc
      _ = (repeated * multiplier) * Q := (mul_assoc _ _ _).symm
      _ = D * Q := by rw [hmultiplier]
      _ = H := by rw [mul_comm, hfactor]
      _ = radical * repeated := EuclideanDomain.radical_mul_divRadical.symm
      _ = repeated * radical := mul_comm _ _
  have hquotientDvd : Q ∣ radical := by
    refine ⟨multiplier, ?_⟩
    have := mul_left_cancel₀ (EuclideanDomain.divRadical_ne_zero hH) hcancel
    simpa [mul_comm] using this.symm
  exact UniqueFactorizationMonoid.squarefree_radical.squarefree_of_dvd hquotientDvd

/-- A successful primitive quotient records its exact localized quotient before denominator and
content clearing. -/
theorem quotientPrimitive_localized {A B R : CBivariate F}
    (h : quotientPrimitive A B = some R) :
    ∃ q, FunctionFieldEuclid.divide (ClearDenominators.embed A)
        (ClearDenominators.embed B) = some q ∧
      Associated (ClearDenominators.valueGlobal R) (FunctionFieldEuclid.value q) ∧
      FunctionFieldEuclid.value q * ClearDenominators.valueGlobal B =
        ClearDenominators.valueGlobal A := by
  unfold quotientPrimitive at h
  cases hq : FunctionFieldEuclid.divide (ClearDenominators.embed A)
      (ClearDenominators.embed B) with
  | none => simp [hq] at h
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at h
    subst R
    refine ⟨q, rfl, ClearDenominators.clear_primitive_associated q, ?_⟩
    have hproduct := ((FunctionFieldEuclid.divide_eq_some_iff _ _ q).mp hq).2
    simpa only [ClearDenominators.value_embed] using hproduct

/-- Over a field, splitting a squarefree polynomial by a divisor associated to its derivative
gcd separates a derivative-zero discarded factor from a separable retained quotient. -/
theorem field_gcd_split {K : Type*} [Field K] [DecidableEq K]
    {H D Q : Polynomial K} (hH : H ≠ 0) (hsquarefree : Squarefree H)
    (hassociated : Associated D (EuclideanDomain.gcd H H.derivative))
    (hfactor : Q * D = H) :
    Squarefree D ∧ Squarefree Q ∧ D.derivative = 0 ∧ Q.Separable := by
  have hDdvdH : D ∣ H := hassociated.dvd.trans (EuclideanDomain.gcd_dvd_left _ _)
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hH hDdvdH
  have hQ : Q ≠ 0 := by
    intro hz
    apply hH
    simpa [hz] using hfactor.symm
  have hDsquarefree : Squarefree D := hsquarefree.squarefree_of_dvd hDdvdH
  have hQsquarefree : Squarefree Q :=
    squarefree_quotient_gcd_derivative hH hassociated hfactor
  have hproductSquarefree : Squarefree (Q * D) := by simpa only [hfactor] using hsquarefree
  have hrel : IsRelPrime Q D := IsRelPrime.of_squarefree_mul hproductSquarefree
  have hDdvdDerivative : D ∣ H.derivative :=
    hassociated.dvd.trans (EuclideanDomain.gcd_dvd_right _ _)
  have hderivative := congrArg Polynomial.derivative hfactor
  rw [Polynomial.derivative_mul] at hderivative
  have hDdvdQD : D ∣ Q * D.derivative := by
    have hterm : D ∣ Q.derivative * D := dvd_mul_left D Q.derivative
    have hsub : D ∣ H.derivative - Q.derivative * D := dvd_sub hDdvdDerivative hterm
    rw [← hderivative, add_sub_cancel_left] at hsub
    exact hsub
  have hDdvdOwnDerivative : D ∣ D.derivative :=
    hrel.symm.dvd_of_dvd_mul_left hDdvdQD
  have hDderivative : D.derivative = 0 := by
    by_contra hn
    have hle := Polynomial.natDegree_le_of_dvd hDdvdOwnDerivative hn
    have hDdegree : D.natDegree ≠ 0 := by
      intro hz
      exact hn (Polynomial.derivative_of_natDegree_zero hz)
    have hlt := Polynomial.natDegree_derivative_lt hDdegree
    omega
  have hQseparable : Q.Separable := by
    apply IsRelPrime.isCoprime
    intro d hdQ hdQderivative
    have hdH : d ∣ H := hdQ.trans ⟨D, hfactor.symm⟩
    have hderivativeFactor : H.derivative = Q.derivative * D := by
      rw [← hderivative, hDderivative, MulZeroClass.mul_zero, add_zero]
    have hdHderivative : d ∣ H.derivative := by
      rw [hderivativeFactor]
      exact dvd_mul_of_dvd_left hdQderivative D
    have hdD : d ∣ D := by
      exact (EuclideanDomain.dvd_gcd hdH hdHderivative).trans hassociated.dvd'
    exact hrel hdQ hdD
  exact ⟨hDsquarefree, hQsquarefree, hDderivative, hQseparable⟩

/-- Complete correctness data for the actual `separablePart` quotient. -/
structure Certificate (support discarded regular : CBivariate F) : Prop where
  /-- The discarded factor is the actually executed descended derivative gcd. -/
  discarded_eq : discarded = globalGcd support (CBivariate.partialDerivY support)
  /-- The checked quotient returned the retained factor. -/
  quotient_eq : separablePart support = some regular
  /-- Neither side of the factor split is zero. -/
  discarded_ne_zero : discarded ≠ 0
  regular_ne_zero : regular ≠ 0
  /-- Both global factors inherit reducedness from the radical. -/
  discarded_squarefree : Squarefree (CBivariate.toPoly discarded)
  regular_squarefree : Squarefree (CBivariate.toPoly regular)
  /-- Exactly the Y-inseparable part is discarded. -/
  discarded_derivative : CBivariate.partialDerivY discarded = 0
  discarded_noGraph : ∀ P : Polynomial F, (CBivariate.toPoly discarded).eval P ≠ 0
  /-- The retained primitive polynomial is separable over `F(X)`. -/
  regular_primitive : (CBivariate.toPoly regular).IsPrimitive
  regular_separable : (ClearDenominators.valueGlobal regular).Separable
  /-- The retained factor divides the radical globally and preserves its graph equation. -/
  regular_dvd_support : CBivariate.toPoly regular ∣ CBivariate.toPoly support
  regular_graph_iff : ∀ P : Polynomial F,
    (CBivariate.toPoly regular).eval P = 0 ↔ (CBivariate.toPoly support).eval P = 0
  /-- Clearing denominators and content records the exact global reconstruction. -/
  reconstruction : ∃ (scale content : CPolynomial F), scale.toPoly ≠ 0 ∧
    content.toPoly ≠ 0 ∧
      (CPolynomial.C content : CPolynomial (CPolynomial F)) *
          (show CPolynomial (CPolynomial F) from discarded) *
          (show CPolynomial (CPolynomial F) from regular) =
        (CPolynomial.C scale : CPolynomial (CPolynomial F)) *
          (show CPolynomial (CPolynomial F) from support)

/-- The actual primitive quotient in `separablePart` succeeds and has the complete separable
split certificate whenever its input is a nonzero primitive global radical. -/
theorem separablePart_certificate {support : CBivariate F} (hsupport : support ≠ 0)
    (hprimitive : (CBivariate.toPoly support).IsPrimitive)
    (hsquarefree : Squarefree (CBivariate.toPoly support)) :
    ∃ discarded regular, Certificate support discarded regular := by
  classical
  let : DecidableEq (RatFunc F) := Classical.decEq _
  let discarded := globalGcd support (CBivariate.partialDerivY support)
  have hdiscarded : discarded ≠ 0 := globalGcd_ne_zero _ _ hsupport
  obtain ⟨regular, hquotient⟩ := quotientPrimitive_eq_some_of_dvd hdiscarded
    (globalGcd_dvd support _ hsupport).1
  obtain ⟨q, hdivide, hregularAssociated, hfactor⟩ :=
    quotientPrimitive_localized hquotient
  have hsupportLocalized : ClearDenominators.valueGlobal support ≠ 0 :=
    valueGlobal_ne_zero hsupport
  have hregular : regular ≠ 0 := by
    intro hz
    have hregularLocalized : ClearDenominators.valueGlobal regular = 0 := by
      simp only [hz, ClearDenominators.valueGlobal_zero]
    have hqzero : FunctionFieldEuclid.value q = 0 :=
      hregularAssociated.eq_zero_iff.mp hregularLocalized
    rw [hqzero, MulZeroClass.zero_mul] at hfactor
    exact hsupportLocalized hfactor.symm
  have hsquarefreeLocalized : Squarefree (ClearDenominators.valueGlobal support) :=
    squarefree_valueGlobal hprimitive hsquarefree
  have hdiscardedAssociated : Associated (ClearDenominators.valueGlobal discarded)
      (EuclideanDomain.gcd (ClearDenominators.valueGlobal support)
        (ClearDenominators.valueGlobal support).derivative) := by
    simpa only [discarded, CBivariate.partialDerivY_toPoly,
      ClearDenominators.valueGlobal, Polynomial.derivative_map] using
      globalGcd_associated support (CBivariate.partialDerivY support)
  obtain ⟨hdiscardedSquarefreeLocalized, hqSquarefree, hdiscardedDerivativeLocalized,
      hqSeparable⟩ := field_gcd_split hsupportLocalized hsquarefreeLocalized
        hdiscardedAssociated hfactor
  have hdiscardedDvd : CBivariate.toPoly discarded ∣ CBivariate.toPoly support :=
    (globalGcd_dvd support _ hsupport).1
  have hregularDvd : CBivariate.toPoly regular ∣ CBivariate.toPoly support :=
    quotientPrimitive_dvd_left_global _ _ _ hquotient hregular
  have hdiscardedSquarefree : Squarefree (CBivariate.toPoly discarded) :=
    hsquarefree.squarefree_of_dvd hdiscardedDvd
  have hregularSquarefree : Squarefree (CBivariate.toPoly regular) :=
    hsquarefree.squarefree_of_dvd hregularDvd
  have hdiscardedDerivative : CBivariate.partialDerivY discarded = 0 := by
    apply valueGlobal_injective (F := F)
    rw [ClearDenominators.valueGlobal_zero]
    rw [ClearDenominators.valueGlobal]
    rw [CBivariate.partialDerivY_toPoly]
    change (CBivariate.toPoly discarded).derivative.map
      (algebraMap (Polynomial F) (RatFunc F)) = 0
    simpa only [ClearDenominators.valueGlobal, Polynomial.derivative_map] using
      hdiscardedDerivativeLocalized
  have hdiscardedDerivativePoly : (CBivariate.toPoly discarded).derivative = 0 := by
    simpa only [CBivariate.partialDerivY_toPoly, CBivariate.toPoly_zero] using
      congrArg CBivariate.toPoly hdiscardedDerivative
  have hdiscardedNoGraph (P : Polynomial F) :
      (CBivariate.toPoly discarded).eval P ≠ 0 :=
    eval_ne_zero_of_squarefree_derivative_zero _ hdiscardedSquarefree
      hdiscardedDerivativePoly P
  have hregularSeparable : (ClearDenominators.valueGlobal regular).Separable :=
    hregularAssociated.separable_iff.mpr hqSeparable
  have hregularGraph (P : Polynomial F) :
      (CBivariate.toPoly regular).eval P = 0 ↔
        (CBivariate.toPoly support).eval P = 0 := by
    have hgraph := quotientPrimitive_graph support discarded regular hquotient P
    rw [mul_eq_zero] at hgraph
    simpa only [hdiscardedNoGraph P, false_or] using hgraph
  exact ⟨discarded, regular,
    ⟨rfl, hquotient, hdiscarded, hregular, hdiscardedSquarefree,
      hregularSquarefree, hdiscardedDerivative, hdiscardedNoGraph,
      quotientPrimitive_isPrimitive _ _ _ hquotient hregular,
      hregularSeparable, hregularDvd, hregularGraph,
      quotientPrimitive_global_identity _ _ _ hquotient⟩⟩

private theorem stored_gcd_derivative_eq_one {regular : CBivariate F}
    (hseparable : (ClearDenominators.valueGlobal regular).Separable) :
    FunctionFieldEuclid.gcd (ClearDenominators.embed regular)
      (ClearDenominators.embed regular).derivative = 1 := by
  classical
  let image := ClearDenominators.embed regular
  have hvalueDerivative : FunctionFieldEuclid.value image.derivative =
      (FunctionFieldEuclid.value image).derivative := by
    simp only [FunctionFieldEuclid.value, CPolynomial.derivative_toPoly,
      Polynomial.derivative_map]
  have hcoprime : IsCoprime (FunctionFieldEuclid.value image)
      (FunctionFieldEuclid.value image.derivative) := by
    rw [hvalueDerivative, ClearDenominators.value_embed]
    exact hseparable
  apply FunctionFieldEuclid.value_injective
  rw [FunctionFieldEuclid.value_gcd]
  rw [normalize_eq_one.mpr (EuclideanDomain.gcd_isUnit_iff.mpr hcoprime)]
  simp only [FunctionFieldEuclid.value, CPolynomial.toPoly_one, Polynomial.map_one]

private theorem obstruction_ne_zero {regular : CBivariate F}
    (hprimitive : (CBivariate.toPoly regular).IsPrimitive)
    (hpositive : 0 < regular.natDegree)
    (hseparable : (ClearDenominators.valueGlobal regular).Separable) :
    RegularCenterObstruction.obstruction regular ≠ 0 := by
  let input : RegularCenterObstruction.Input F :=
    ⟨regular, hprimitive, hpositive, hseparable⟩
  exact RegularCenterObstruction.obstruction_ne_zero input

/-- Original-relative facts inherited by the retained separable factor. -/
structure FinalCertificate (original support discarded regular : CBivariate F) : Prop extends
    Certificate support discarded regular where
  regular_dvd_original : CBivariate.toPoly regular ∣ CBivariate.toPoly original
  regular_natDegree_le_original : regular.natDegree ≤ original.natDegree
  regular_degreeX_le_original :
    Polynomial.Bivariate.degreeX (CBivariate.toPoly regular) ≤
      Polynomial.Bivariate.degreeX (CBivariate.toPoly original)
  regular_graph_iff_original : ∀ P : Polynomial F,
    (CBivariate.toPoly regular).eval P = 0 ↔ (CBivariate.toPoly original).eval P = 0

/-- A radical certificate forces the actual `finish` computation into its mathematically correct
branch.  A constant retained factor certifies that the original has no polynomial graph.  A
positive-degree retained factor passes the executed stored gcd and obstruction tests and returns
`normalized`. -/
theorem finish_of_radical_certificate {original support : CBivariate F}
    (horiginal : original ≠ 0) (hsupport : support ≠ 0)
    (hprimitive : (CBivariate.toPoly support).IsPrimitive)
    (hsquarefree : Squarefree (CBivariate.toPoly support))
    (hsupportDvd : CBivariate.toPoly support ∣ CBivariate.toPoly original)
    (hgraph : ∀ P : Polynomial F,
      (CBivariate.toPoly support).eval P = 0 ↔
        (CBivariate.toPoly original).eval P = 0) :
    ∃ discarded regular, FinalCertificate original support discarded regular ∧
      let data : Data F := ⟨original, support, discarded, regular,
        RegularCenterObstruction.obstruction regular⟩
      (regular.natDegree = 0 ∧ finish original support = .constantRegularPart data ∧
          ∀ P : Polynomial F, (CBivariate.toPoly original).eval P ≠ 0) ∨
        (0 < regular.natDegree ∧
          FunctionFieldEuclid.gcd (ClearDenominators.embed regular)
            (ClearDenominators.embed regular).derivative = 1 ∧
          RegularCenterObstruction.obstruction regular ≠ 0 ∧
          finish original support = .normalized data) := by
  classical
  obtain ⟨discarded, regular, hsplit⟩ :=
    separablePart_certificate hsupport hprimitive hsquarefree
  have horiginalPoly : CBivariate.toPoly original ≠ 0 := toPoly_ne_zero horiginal
  have hregularDvdOriginal : CBivariate.toPoly regular ∣ CBivariate.toPoly original :=
    hsplit.regular_dvd_support.trans hsupportDvd
  have hregularNatDegree : regular.natDegree ≤ original.natDegree := by
    have hpolyDegree : (CBivariate.toPoly regular).natDegree ≤
        (CBivariate.toPoly original).natDegree :=
      Polynomial.natDegree_le_of_dvd hregularDvdOriginal horiginalPoly
    calc
      regular.natDegree = (CBivariate.toPoly regular).natDegree := by
        simpa only [CBivariate.natDegreeY] using
          (CBivariate.natDegreeY_toPoly regular).symm
      _ ≤ (CBivariate.toPoly original).natDegree := hpolyDegree
      _ = original.natDegree := by
        simpa only [CBivariate.natDegreeY] using
          CBivariate.natDegreeY_toPoly original
  have hregularDegreeX :=
    Polynomial.Bivariate.degreeX_le_of_dvd hregularDvdOriginal horiginalPoly
  have hregularGraph (P : Polynomial F) :
      (CBivariate.toPoly regular).eval P = 0 ↔
        (CBivariate.toPoly original).eval P = 0 :=
    (hsplit.regular_graph_iff P).trans (hgraph P)
  have hfinal : FinalCertificate original support discarded regular :=
    ⟨hsplit, hregularDvdOriginal, hregularNatDegree, hregularDegreeX, hregularGraph⟩
  refine ⟨discarded, regular, hfinal, ?_⟩
  by_cases hdegree : regular.natDegree = 0
  · left
    refine ⟨hdegree, ?_, ?_⟩
    · unfold finish
      dsimp only
      rw [← hsplit.discarded_eq, hsplit.quotient_eq]
      simp only [hdegree, beq_self_eq_true, ↓reduceIte]
    · intro P horiginalRoot
      have hregularRoot : (CBivariate.toPoly regular).eval P = 0 :=
        (hregularGraph P).mpr horiginalRoot
      have hregularPolyDegree : (CBivariate.toPoly regular).natDegree = 0 := by
        calc
          _ = regular.natDegree := by
            simpa only [CBivariate.natDegreeY] using
              CBivariate.natDegreeY_toPoly regular
          _ = 0 := hdegree
      have hregularPoly : CBivariate.toPoly regular ≠ 0 :=
        toPoly_ne_zero hsplit.regular_ne_zero
      rw [Polynomial.eq_C_of_natDegree_eq_zero hregularPolyDegree,
        Polynomial.eval_C] at hregularRoot
      apply hregularPoly
      rw [Polynomial.eq_C_of_natDegree_eq_zero hregularPolyDegree]
      rw [hregularRoot, Polynomial.C_0]
  · right
    have hpositive : 0 < regular.natDegree := Nat.pos_of_ne_zero hdegree
    have hgcd := stored_gcd_derivative_eq_one hsplit.regular_separable
    have hobstruction := obstruction_ne_zero hsplit.regular_primitive hpositive
      hsplit.regular_separable
    refine ⟨hpositive, hgcd, hobstruction, ?_⟩
    unfold finish
    dsimp only
    rw [← hsplit.discarded_eq, hsplit.quotient_eq]
    have hdegreeCheck : (regular.natDegree == 0) = false :=
      beq_eq_false_iff_ne.mpr hdegree
    have hobstructionCheck :
        (RegularCenterObstruction.obstruction regular == 0) = false :=
      beq_eq_false_iff_ne.mpr hobstruction
    simp only [hdegreeCheck, Bool.false_eq_true, ↓reduceIte, hgcd,
      bne_self_eq_false, hobstructionCheck]

end Polynomial.FunctionFieldAlgorithms.SeparablePartCorrectness
