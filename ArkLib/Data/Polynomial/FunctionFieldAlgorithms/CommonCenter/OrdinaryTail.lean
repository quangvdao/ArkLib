/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.RegularPart
public import ArkLib.ToMathlib.Polynomial.PaddedDerivativeResultantCommonRoot

/-!
# Content and resultant ordinary tail

The coefficient field in this module is the first-order coefficient field, so the inner
variable is the message state and the outer variable is its derivative state. In particular,
inner-variable content is retained in the ordinary equation, rather than discarded as if it
were content in the original challenge variable.

This is the primitive-state preparation variant: message-only content is retained with its
original multiplicities. The output is a nonzero ordinary equation, before denominator
clearing and ordinary `SeparablePart`. Conversion of a supplied trivariate interpolant into
the stored function-field coefficient representation belongs to a separate adapter.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.OrdinaryTail

open CompPoly CPolynomial CPoly
open OrdinaryNormalization NormalizationArithmetic RadicalCorrectness SeparablePartCorrectness

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance : DecidableEq F := instDecidableEqOfLawfulBEq

/-- Values computed before constructing a common-center normal module. -/
structure Data (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  /-- The supplied state equation. -/
  original : CBivariate F
  /-- Message-only content, retained for the ordinary branch. -/
  content : CPolynomial F
  /-- Primitive state equation before repeated-factor removal. -/
  core : CBivariate F
  /-- Reduced primitive state support. -/
  support : CBivariate F
  /-- Actual gcd with the derivative in the highest state variable. -/
  discarded : CBivariate F
  /-- Actual primitive quotient by that gcd. -/
  regular : CBivariate F
  /-- Message-only equation covering content and singular regular states. -/
  ordinary : CPolynomial F

/-- Explicit exceptional cases of state preparation. -/
inductive Result (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  | zeroEquation
  | prepared (data : Data F)
  | arithmeticFailure (reason : OrdinaryNormalization.Failure)

/-- Retain content and the constant coefficient of the derivative-zero gcd. The small-degree
correctness theorem establishes that the latter is its entire polynomial. -/
def finish (original core support : CBivariate F) : Result F :=
  let content := ClearDenominators.primitiveContent original
  let discarded := globalGcd support (CBivariate.partialDerivY support)
  match separablePart support with
  | none => .arithmeticFailure .quotient
  | some regular =>
    let ordinary := content * CPolynomial.coeff discarded 0 *
      (if regular.natDegree == 0 then 1 else
        RegularCenterObstruction.derivativeResultant regular)
    .prepared ⟨original, content, core, support, discarded, regular, ordinary⟩

/-- Remove repeated state factors using the actual characteristic. Constant state equations
bypass radicalization and leave all their content in the ordinary equation. -/
def run (p : ℕ) (inverse : F → F) (equation : CBivariate F) : Result F :=
  if equation == 0 then .zeroEquation
  else
    let core := ClearDenominators.primitivePart equation
    if core.natDegree == 0 then finish equation core 1
    else match radical p inverse core.natDegree core with
      | .error reason => .arithmeticFailure reason
      | .ok support => finish equation core support

/-- A derivative-zero polynomial of degree below the characteristic is constant. -/
theorem eq_C_of_derivative_eq_zero_of_degree_lt
    {R : Type*} [CommRing R] [IsDomain R] (p : ℕ) [CharP R p]
    (A : Polynomial R) (hdegree : A.natDegree < p) (hd : A.derivative = 0) :
    A = Polynomial.C (A.coeff 0) := by
  apply Polynomial.ext
  intro n
  cases n with
  | zero => simp
  | succ n =>
    rw [Polynomial.coeff_C, if_neg (Nat.succ_ne_zero n)]
    by_cases hn : n + 1 ≤ A.natDegree
    · have hcoeff := congrArg (fun B : Polynomial R => B.coeff n) hd
      rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hcoeff
      have hcast : (↑(n + 1) : R) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff R p]
        exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos n) (lt_of_le_of_lt hn hdegree)
      exact (mul_eq_zero.mp hcoeff).resolve_right
        (by simpa only [Nat.cast_add, Nat.cast_one] using hcast)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- The discarded gcd becomes a nonvanishing scalar polynomial under the state-degree guard.
This uses the actual gcd, including the case where the reduced regular part is constant. -/
theorem discarded_constant (p : ℕ) [CharP F p]
    {support discarded regular : CBivariate F}
    (cert : SeparablePartCorrectness.Certificate support discarded regular)
    (hsupport : support ≠ 0) (hdegree : support.natDegree < p) :
    CBivariate.toPoly discarded = Polynomial.C ((CBivariate.toPoly discarded).coeff 0) := by
  have hdvd : CBivariate.toPoly discarded ∣ CBivariate.toPoly support := by
    rw [cert.discarded_eq]
    exact (globalGcd_dvd support _ hsupport).1
  have hn : CBivariate.toPoly support ≠ 0 := by
    intro hz
    apply hsupport
    apply CBivariate.ringEquiv.injective
    change CBivariate.toPoly support = CBivariate.toPoly 0
    simpa only [CBivariate.toPoly_zero] using hz
  apply eq_C_of_derivative_eq_zero_of_degree_lt p
  · exact lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hdvd hn)
      (by simpa only [stored_natDegree_eq] using hdegree)
  · simpa only [CBivariate.partialDerivY_toPoly, CBivariate.toPoly_zero] using
      congrArg CBivariate.toPoly cert.discarded_derivative

/-- A common root of the regular equation and its separant lies on the computed ordinary
resultant, even when specialization lowers the state degree. -/
theorem derivativeResultant_eq_zero_of_common_root
    (regular : CBivariate F) (hdegree : 0 < regular.natDegree)
    {K : Type*} [Field K] (embedding : F →+* K) (u v : K)
    (hroot : RegularPart.evalAt embedding u v regular = 0)
    (hderivative : RegularPart.evalAt embedding u v
      (CBivariate.partialDerivY regular) = 0) :
    (RegularCenterObstruction.derivativeResultant regular).toPoly.eval₂ embedding u = 0 := by
  have h := Polynomial.paddedDerivativeResultant_map_eq_zero_of_common_root
    (CBivariate.toPoly regular) hdegree (by rw [← stored_natDegree_eq])
    (Polynomial.eval₂RingHom embedding u) v
    (by simpa only [Polynomial.eval_map, RegularPart.evalAt] using hroot)
    (by simpa only [Polynomial.derivative_map, Polynomial.eval_map,
      RegularPart.evalAt, CBivariate.partialDerivY_toPoly] using hderivative)
  simpa only [RegularCenterObstruction.derivativeResultant_toPoly,
    Polynomial.separableResultant, Polynomial.paddedDerivativeResultant,
    Polynomial.coe_eval₂RingHom] using h

private theorem toPoly_C (c : CPolynomial F) :
    CBivariate.toPoly (CPolynomial.C c : CBivariate F) = Polynomial.C c.toPoly := by
  rw [CBivariate.toPoly_eq_map, CPolynomial.C_toPoly, Polynomial.map_C]
  congr 1
  exact CPolynomial.ringEquiv_apply _

omit [BEq F] [LawfulBEq F] in
private theorem evalAt_zero_of_dvd {K : Type*} [Field K] (embedding : F →+* K)
    (u v : K) {A B : (Polynomial F)[X]} (h : A ∣ B)
    (ha : A.eval₂ (Polynomial.eval₂RingHom embedding u) v = 0) :
    B.eval₂ (Polynomial.eval₂RingHom embedding u) v = 0 := by
  obtain ⟨Q, rfl⟩ := h
  simp only [Polynomial.eval₂_mul, ha, MulZeroClass.zero_mul]

private theorem primitive_constant_no_root {regular : CBivariate F}
    (hp : (CBivariate.toPoly regular).IsPrimitive) (hd : regular.natDegree = 0)
    {K : Type*} [Field K] (embedding : F →+* K) (u v : K) :
    RegularPart.evalAt embedding u v regular ≠ 0 := by
  have heq := Polynomial.eq_C_of_natDegree_eq_zero
    (show (CBivariate.toPoly regular).natDegree = 0 by
      simpa only [stored_natDegree_eq] using hd)
  have hu : IsUnit ((CBivariate.toPoly regular).coeff 0) :=
    hp _ ⟨1, by simpa only [mul_one] using heq⟩
  rw [RegularPart.evalAt, heq, Polynomial.eval₂_C]
  exact (hu.map (Polynomial.eval₂RingHom embedding u)).ne_zero

/-- The finished state split covers every reduced state by its computed ordinary equation or
by its regular equation with nonzero separant. -/
theorem finish_partition (p : ℕ) [CharP F p]
    (original core support : CBivariate F) (data : Data F)
    (hsupport : support ≠ 0) (hp : (CBivariate.toPoly support).IsPrimitive)
    (hs : Squarefree (CBivariate.toPoly support)) (hd : support.natDegree < p)
    (hrun : finish original core support = .prepared data)
    {K : Type*} [Field K] (embedding : F →+* K) (u v : K)
    (hroot : RegularPart.evalAt embedding u v support = 0) :
    data.ordinary.toPoly.eval₂ embedding u = 0 ∨
      (RegularPart.evalAt embedding u v data.regular = 0 ∧
        RegularPart.evalAt embedding u v (CBivariate.partialDerivY data.regular) ≠ 0) := by
  classical
  obtain ⟨discarded, regular, cert⟩ := separablePart_certificate hsupport hp hs
  have hdiscarded := discarded_constant p cert hsupport hd
  have hq : quotientPrimitive support discarded = some regular := by
    simpa only [separablePart, ← cert.discarded_eq] using cert.quotient_eq
  have hsupportDvd : CBivariate.toPoly support ∣ CBivariate.toPoly (discarded * regular) := by
    apply primitive_dvd_of_valueGlobal_dvd hp
    rw [ClearDenominators.valueGlobal_mul]
    simpa only [NormalizationMultiplicity.localized, mul_comm] using
      (NormalizationMultiplicity.quotientPrimitive_localized_mul_associated
        support discarded regular hq).dvd'
  have hproduct := evalAt_zero_of_dvd embedding u v hsupportDvd hroot
  rw [CBivariate.toPoly_mul, Polynomial.eval₂_mul] at hproduct
  have hdiscardedEval : RegularPart.evalAt embedding u v discarded =
      (CPolynomial.coeff discarded 0).toPoly.eval₂ embedding u := by
    rw [RegularPart.evalAt, hdiscarded, Polynomial.eval₂_C]
    rw [CBivariate.toPoly_coeff, Polynomial.coe_eval₂RingHom]
  unfold finish at hrun
  rw [cert.quotient_eq, ← cert.discarded_eq] at hrun
  cases hrun
  dsimp only
  rcases mul_eq_zero.mp hproduct with hw | hr
  · left
    have hw' : (CPolynomial.coeff discarded 0).toPoly.eval₂ embedding u = 0 :=
      hdiscardedEval ▸ hw
    simp only [CPolynomial.toPoly_mul, Polynomial.eval₂_mul, hw',
      MulZeroClass.mul_zero, MulZeroClass.zero_mul]
  · by_cases hregular : regular.natDegree = 0
    · exact False.elim ((primitive_constant_no_root cert.regular_primitive hregular
        embedding u v) hr)
    · by_cases hsep : RegularPart.evalAt embedding u v (CBivariate.partialDerivY regular) = 0
      · left
        have hz := derivativeResultant_eq_zero_of_common_root regular
          (Nat.pos_of_ne_zero hregular) embedding u v hr hsep
        simp only [show (regular.natDegree == 0) = false by simp [hregular],
          Bool.false_eq_true, ↓reduceIte, CPolynomial.toPoly_mul, Polynomial.eval₂_mul,
          hz, MulZeroClass.mul_zero]
      · exact Or.inr ⟨hr, hsep⟩

/-- The ordinary equation returned after the reduced-state split is nonzero. -/
theorem finish_ordinary_ne_zero (p : ℕ) [CharP F p]
    (original core support : CBivariate F) (data : Data F)
    (hsupport : support ≠ 0) (hp : (CBivariate.toPoly support).IsPrimitive)
    (hs : Squarefree (CBivariate.toPoly support)) (hd : support.natDegree < p)
    (hrun : finish original core support = .prepared data) : data.ordinary ≠ 0 := by
  classical
  obtain ⟨discarded, regular, cert⟩ := separablePart_certificate hsupport hp hs
  have hc := discarded_constant p cert hsupport hd
  have hw : CPolynomial.coeff discarded 0 ≠ 0 := by
    intro hz
    apply cert.discarded_ne_zero
    apply CBivariate.ringEquiv.injective
    change CBivariate.toPoly discarded = CBivariate.toPoly 0
    rw [hc, CBivariate.toPoly_coeff, hz, CPolynomial.toPoly_zero, Polynomial.C_0,
      CBivariate.toPoly_zero]
  have hcontent : ClearDenominators.primitiveContent original ≠ 0 := by
    intro hz
    exact ClearDenominators.primitiveContent_ne_zero original
      (by rw [hz, CPolynomial.toPoly_zero])
  unfold finish at hrun
  rw [cert.quotient_eq, ← cert.discarded_eq] at hrun
  cases hrun
  dsimp only
  have hlast : (if regular.natDegree == 0 then 1 else
      RegularCenterObstruction.derivativeResultant regular) ≠ 0 := by
    split
    · intro hz
      have ht := congrArg CPolynomial.toPoly hz
      simp [CPolynomial.toPoly_one, CPolynomial.toPoly_zero] at ht
    · rename_i hn
      exact RegularCenterObstruction.derivativeResultant_ne_zero
        ⟨regular, cert.regular_primitive,
          Nat.pos_of_ne_zero (by simpa only [beq_iff_eq] using hn), cert.regular_separable⟩
  intro hz
  have ht := congrArg CPolynomial.toPoly hz
  rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_mul, CPolynomial.toPoly_zero] at ht
  exact (mul_ne_zero (mul_ne_zero
    ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hcontent)
    ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hw))
    ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hlast)) ht

/-- The computed radical and exact quotient cannot fail under the supplied inverse-Frobenius
law. This is an actual-run theorem, with no success or factorization input. -/
theorem run_success (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (equation : CBivariate F) (hequation : equation ≠ 0)
    (hinverse : p ≤ (ClearDenominators.primitivePart equation).natDegree →
      ∀ a, inverse a ^ p = a) :
    ∃ data, run p inverse equation = .prepared data := by
  classical
  let core := ClearDenominators.primitivePart equation
  have hcore : core ≠ 0 := primitivePart_ne_zero hequation
  have hprimitive := primitivePart_isPrimitive hequation
  have finish_success (support : CBivariate F) (hsupport : support ≠ 0)
      (hp : (CBivariate.toPoly support).IsPrimitive)
      (hs : Squarefree (CBivariate.toPoly support)) :
      ∃ data, finish equation core support = .prepared data := by
    obtain ⟨discarded, regular, cert⟩ := separablePart_certificate hsupport hp hs
    unfold finish
    rw [cert.quotient_eq]
    exact ⟨_, rfl⟩
  rw [run, if_neg (by simpa using hequation)]
  dsimp only
  by_cases hd : core.natDegree = 0
  · rw [if_pos (by simpa [core] using hd)]
    apply finish_success 1
    · intro hz
      have ht := congrArg CBivariate.toPoly hz
      simp [CBivariate.toPoly_one, CBivariate.toPoly_zero] at ht
    · simpa only [CBivariate.toPoly_one] using
        (Polynomial.isPrimitive_one (R := Polynomial F))
    · simpa only [CBivariate.toPoly_one] using (squarefree_one : Squarefree (1 : (Polynomial F)[X]))
  · rw [if_neg (by simpa [core] using hd)]
    obtain ⟨support, hr, cert⟩ := radical_certificate p core.natDegree inverse
      (by simpa [core] using hinverse) core hcore hprimitive
      (by rw [← stored_natDegree_eq]) hd
    rw [show ClearDenominators.primitivePart equation = core from rfl, hr]
    exact finish_success support cert.output_ne_zero cert.output_isPrimitive cert.output_squarefree

/-- Every successful small-state run exports the actual gcd/quotient certificate needed by
regular-curve consumers, including primitivity, squarefreeness, and separability. -/
theorem run_separable_certificate (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (equation : CBivariate F) (hequation : equation ≠ 0)
    (hdegree : (ClearDenominators.primitivePart equation).natDegree < p)
    (data : Data F) (hrun : run p inverse equation = .prepared data) :
    SeparablePartCorrectness.Certificate data.support data.discarded data.regular := by
  classical
  let core := ClearDenominators.primitivePart equation
  have finish_cert (support : CBivariate F) (hn : support ≠ 0)
      (hp : (CBivariate.toPoly support).IsPrimitive)
      (hs : Squarefree (CBivariate.toPoly support))
      (hr : finish equation core support = .prepared data) :
      SeparablePartCorrectness.Certificate data.support data.discarded data.regular := by
    obtain ⟨discarded, regular, cert⟩ := separablePart_certificate hn hp hs
    unfold finish at hr
    rw [cert.quotient_eq, ← cert.discarded_eq] at hr
    cases hr
    exact cert
  rw [run, if_neg (by simpa using hequation)] at hrun
  dsimp only at hrun
  by_cases hd : core.natDegree = 0
  · rw [if_pos (by simpa [core] using hd)] at hrun
    apply finish_cert 1 _
      (by simpa only [CBivariate.toPoly_one] using
        (Polynomial.isPrimitive_one (R := Polynomial F)))
      (by simpa only [CBivariate.toPoly_one] using
        (squarefree_one : Squarefree (1 : (Polynomial F)[X]))) hrun
    intro hz
    have ht := congrArg CBivariate.toPoly hz
    simp [CBivariate.toPoly_one, CBivariate.toPoly_zero] at ht
  · rw [if_neg (by simpa [core] using hd)] at hrun
    obtain ⟨support, hr, cert⟩ := radical_certificate p core.natDegree inverse
      (fun h => False.elim (Nat.not_le_of_gt hdegree h)) core
      (primitivePart_ne_zero hequation) (primitivePart_isPrimitive hequation)
      (by rw [← stored_natDegree_eq]) hd
    rw [show ClearDenominators.primitivePart equation = core from rfl, hr] at hrun
    exact finish_cert support cert.output_ne_zero cert.output_isPrimitive
      cert.output_squarefree hrun

private theorem finish_content_root (original core support : CBivariate F) (data : Data F)
    (hrun : finish original core support = .prepared data)
    {K : Type*} [Field K] (embedding : F →+* K) (u : K)
    (hcontent : (ClearDenominators.primitiveContent original).toPoly.eval₂ embedding u = 0) :
    data.ordinary.toPoly.eval₂ embedding u = 0 := by
  unfold finish at hrun
  split at hrun
  · cases hrun
  · cases hrun
    simp only [CPolynomial.toPoly_mul, Polynomial.eval₂_mul, hcontent, MulZeroClass.zero_mul]

/-- Every wanted state of the actual supplied equation lies on the computed ordinary tail or
on the computed regular curve with nonzero separant. In a function-field application, take
`u = P` and `v = P'`; no agreement or Johnson premise is used. -/
theorem run_partition (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (equation : CBivariate F) (hequation : equation ≠ 0)
    (hdegree : (ClearDenominators.primitivePart equation).natDegree < p)
    (data : Data F) (hrun : run p inverse equation = .prepared data)
    {K : Type*} [Field K] (embedding : F →+* K) (u v : K)
    (hroot : RegularPart.evalAt embedding u v equation = 0) :
    data.ordinary.toPoly.eval₂ embedding u = 0 ∨
      (RegularPart.evalAt embedding u v data.regular = 0 ∧
        RegularPart.evalAt embedding u v (CBivariate.partialDerivY data.regular) ≠ 0) := by
  classical
  let core := ClearDenominators.primitivePart equation
  have hcore : core ≠ 0 := primitivePart_ne_zero hequation
  have hp : (CBivariate.toPoly core).IsPrimitive := primitivePart_isPrimitive hequation
  have hfactor :
      (ClearDenominators.primitiveContent equation).toPoly.eval₂ embedding u *
        RegularPart.evalAt embedding u v core = 0 := by
    have h := congrArg CBivariate.toPoly
      (ClearDenominators.content_mul_primitivePart equation)
    rw [CBivariate.toPoly_mul, toPoly_C] at h
    have heval := congrArg (fun B : (Polynomial F)[X] =>
      B.eval₂ (Polynomial.eval₂RingHom embedding u) v) h
    rw [show (CBivariate.toPoly equation).eval₂
      (Polynomial.eval₂RingHom embedding u) v = 0 from hroot] at heval
    simpa only [Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.coe_eval₂RingHom, RegularPart.evalAt, core] using heval
  rw [run, if_neg (by simpa using hequation)] at hrun
  dsimp only at hrun
  by_cases hd : core.natDegree = 0
  · rw [if_pos (by simpa [core] using hd)] at hrun
    left
    apply finish_content_root equation core 1 data hrun embedding u
    exact (mul_eq_zero.mp hfactor).resolve_right
      (primitive_constant_no_root hp hd embedding u v)
  · rw [if_neg (by simpa [core] using hd)] at hrun
    obtain ⟨support, hr, cert⟩ := radical_certificate p core.natDegree inverse
      (fun h => False.elim (Nat.not_le_of_gt hdegree h)) core hcore hp
      (by rw [← stored_natDegree_eq]) hd
    rw [show ClearDenominators.primitivePart equation = core from rfl, hr] at hrun
    rcases mul_eq_zero.mp hfactor with hc | hc
    · exact Or.inl (finish_content_root equation core support data hrun embedding u hc)
    · have hsroot : RegularPart.evalAt embedding u v support = 0 := by
        have hz := evalAt_zero_of_dvd embedding u v cert.input_dvd_output_pow hc
        rw [Polynomial.eval₂_pow] at hz
        exact (pow_eq_zero_iff hd).mp hz
      apply finish_partition p equation core support data cert.output_ne_zero
        cert.output_isPrimitive cert.output_squarefree _ hrun embedding u v hsroot
      exact lt_of_le_of_lt (by simpa only [stored_natDegree_eq] using cert.natDegree_le)
        hdegree

/-- A successful small-state run returns a nonzero ordinary equation, so subsequent ordinary
normalization is never fed the zero equation. -/
theorem run_ordinary_ne_zero (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (equation : CBivariate F) (hequation : equation ≠ 0)
    (hdegree : (ClearDenominators.primitivePart equation).natDegree < p)
    (data : Data F) (hrun : run p inverse equation = .prepared data) :
    data.ordinary ≠ 0 := by
  classical
  let core := ClearDenominators.primitivePart equation
  rw [run, if_neg (by simpa using hequation)] at hrun
  dsimp only at hrun
  by_cases hd : core.natDegree = 0
  · rw [if_pos (by simpa [core] using hd)] at hrun
    apply finish_ordinary_ne_zero p equation core 1 data (by
      intro hz
      have ht := congrArg CBivariate.toPoly hz
      simp [CBivariate.toPoly_one, CBivariate.toPoly_zero] at ht)
      (by simpa only [CBivariate.toPoly_one] using
        (Polynomial.isPrimitive_one (R := Polynomial F)))
      (by simpa only [CBivariate.toPoly_one] using
        (squarefree_one : Squarefree (1 : (Polynomial F)[X]))) _ hrun
    simpa only [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_one, Polynomial.natDegree_one]
      using (Fact.out : p.Prime).pos
  · rw [if_neg (by simpa [core] using hd)] at hrun
    obtain ⟨support, hr, cert⟩ := radical_certificate p core.natDegree inverse
      (fun h => False.elim (Nat.not_le_of_gt hdegree h)) core
      (primitivePart_ne_zero hequation) (primitivePart_isPrimitive hequation)
      (by rw [← stored_natDegree_eq]) hd
    rw [show ClearDenominators.primitivePart equation = core from rfl, hr] at hrun
    apply finish_ordinary_ne_zero p equation core support data cert.output_ne_zero
      cert.output_isPrimitive cert.output_squarefree _ hrun
    exact lt_of_le_of_lt (by simpa only [stored_natDegree_eq] using cert.natDegree_le)
      hdegree

/-- Certified small-state input always produces a tail/regular partition. The inverse map is
never needed in this characteristic range and can be any executable function. -/
theorem run_exists_partition (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (equation : CBivariate F) (hequation : equation ≠ 0)
    (hdegree : (ClearDenominators.primitivePart equation).natDegree < p) :
    ∃ data, run p inverse equation = .prepared data ∧
      ∀ {K : Type*} [Field K] (embedding : F →+* K) (u v : K),
        RegularPart.evalAt embedding u v equation = 0 →
        data.ordinary.toPoly.eval₂ embedding u = 0 ∨
          (RegularPart.evalAt embedding u v data.regular = 0 ∧
            RegularPart.evalAt embedding u v (CBivariate.partialDerivY data.regular) ≠ 0) := by
  obtain ⟨data, hr⟩ := run_success p inverse equation hequation
    (fun h => False.elim (Nat.not_le_of_gt hdegree h))
  refine ⟨data, hr, ?_⟩
  intro K instK embedding u v h
  exact run_partition p inverse equation hequation hdegree data hr embedding u v h

end Polynomial.FunctionFieldAlgorithms.CommonCenter.OrdinaryTail
