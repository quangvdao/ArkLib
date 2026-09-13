/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.RadicalCorrectness
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.SeparablePartCorrectness

/-!
# Computed regular part of a bivariate equation

This module implements the first-order regular-component reduction used by the fast Taylor
constructor.  It computes the reduced support of the primitive bivariate equation, computes its
actual gcd with a supplied separant, and performs checked exact division.  All gcds are executed
over the stored function field and descended to primitive global polynomials.

The exported reconstruction and point-coverage theorems are global in `F[U][V]`.  Consequently
they remain valid on fibers where an intermediate denominator or a projection discriminant
vanishes.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.RegularPart

open CompPoly CPolynomial CPoly
open BivariateReducedSupport OrdinaryNormalization NormalizationArithmetic
open RadicalCorrectness SeparablePartCorrectness

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- All inspectable values produced by first-order regular-component reduction. -/
structure Data (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  /-- The supplied specialized equation. -/
  original : CBivariate F
  /-- The supplied actual specialized highest-jet partial. -/
  separant : CBivariate F
  /-- The primitive part on which bivariate radicalization is executed. -/
  core : CBivariate F
  /-- The computed reduced support of `core`. -/
  support : CBivariate F
  /-- The computed gcd of `support` and `separant`. -/
  discarded : CBivariate F
  /-- The checked primitive exact quotient `support / discarded`. -/
  regular : CBivariate F

/-- Arithmetic failures remain explicit in the raw executable interface. -/
inductive Failure where
  | radical (reason : OrdinaryNormalization.Failure)
  | quotient
  deriving BEq, Repr

/-- The producer distinguishes the zero equation, an empty regular part, and a nonconstant
regular component union. -/
inductive Result (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  | zeroEquation
  | emptyRegularPart (data : Data F)
  | regularPart (data : Data F)
  | arithmeticFailure (reason : Failure)

/-- Finish a computed radical by gcd removal and checked exact division. -/
def finish (original separant core support : CBivariate F) : Result F :=
  let discarded := globalGcd support separant
  match quotientPrimitive support discarded with
  | none => .arithmeticFailure .quotient
  | some regular =>
      let data : Data F := ⟨original, separant, core, support, discarded, regular⟩
      if regular.natDegree == 0 then .emptyRegularPart data else .regularPart data

/-- Compute the first-order regular part.  Constant primitive cores have no component on which
the actual outer-variable separant can be nonzero, so they directly produce the empty branch. -/
def run (p : ℕ) (inverse : F → F) (equation separant : CBivariate F) : Result F :=
  if equation == 0 then .zeroEquation
  else
    let core := ClearDenominators.primitivePart equation
    if core.natDegree == 0 then
      .emptyRegularPart ⟨equation, separant, core, 1, 1, 1⟩
    else
      match radical p inverse core.natDegree core with
      | .error reason => .arithmeticFailure (.radical reason)
      | .ok support => finish equation separant core support

/-- Evaluate a stored global bivariate polynomial at an arbitrary extension point. -/
noncomputable def evalAt {K : Type*} [Field K] (embedding : F →+* K) (u v : K)
    (h : CBivariate F) : K :=
  (CBivariate.toPoly h).eval₂ (Polynomial.eval₂RingHom embedding u) v

private theorem evalAt_mul {K : Type*} [Field K] (embedding : F →+* K) (u v : K)
    (a b : CBivariate F) :
    evalAt embedding u v (a * b) = evalAt embedding u v a * evalAt embedding u v b := by
  simp only [evalAt, CBivariate.toPoly_mul, Polynomial.eval₂_mul]

private theorem evalAt_pow {K : Type*} [Field K] (embedding : F →+* K) (u v : K)
    (a : CBivariate F) (n : ℕ) :
    evalAt embedding u v (a ^ n) = evalAt embedding u v a ^ n := by
  let _ : DecidableEq F := instDecidableEqOfLawfulBEq
  have hpow : CBivariate.toPoly (a ^ n) = CBivariate.toPoly a ^ n :=
    map_pow CBivariate.ringEquiv a n
  simp only [evalAt, hpow, Polynomial.eval₂_pow]

private theorem evalAt_zero_of_dvd {K : Type*} [Field K] (embedding : F →+* K)
    (u v : K) {a b : CBivariate F} (hab : CBivariate.toPoly a ∣ CBivariate.toPoly b)
    (ha : evalAt embedding u v a = 0) : evalAt embedding u v b = 0 := by
  obtain ⟨q, hq⟩ := hab
  rw [evalAt, hq, Polynomial.eval₂_mul]
  change evalAt embedding u v a * _ = 0
  rw [ha, MulZeroClass.zero_mul]

private theorem toPoly_ne_zero {h : CBivariate F} (hh : h ≠ 0) :
    CBivariate.toPoly h ≠ 0 := by
  let _ : DecidableEq F := instDecidableEqOfLawfulBEq
  intro hz
  apply hh
  apply CBivariate.ringEquiv.injective
  change CBivariate.toPoly h = CBivariate.toPoly 0
  simpa only [CBivariate.toPoly_zero] using hz

/-- Semantic certificate for the executed gcd and exact-division stage. -/
structure SplitCertificate (support separant discarded regular : CBivariate F) : Prop where
  discarded_eq : discarded = globalGcd support separant
  quotient_eq : quotientPrimitive support discarded = some regular
  discarded_ne_zero : discarded ≠ 0
  regular_ne_zero : regular ≠ 0
  discarded_dvd_support : CBivariate.toPoly discarded ∣ CBivariate.toPoly support
  discarded_dvd_separant : CBivariate.toPoly discarded ∣ CBivariate.toPoly separant
  regular_dvd_support : CBivariate.toPoly regular ∣ CBivariate.toPoly support
  reconstruction : Associated
    (CBivariate.toPoly discarded * CBivariate.toPoly regular) (CBivariate.toPoly support)
  regular_isPrimitive : (CBivariate.toPoly regular).IsPrimitive
  regular_squarefree : Squarefree (CBivariate.toPoly regular)
  regular_coprime_separant : IsCoprime
    (ClearDenominators.valueGlobal regular) (ClearDenominators.valueGlobal separant)
  regular_natDegree_le : (CBivariate.toPoly regular).natDegree ≤
    (CBivariate.toPoly support).natDegree
  regular_degreeX_le : Polynomial.Bivariate.degreeX (CBivariate.toPoly regular) ≤
    Polynomial.Bivariate.degreeX (CBivariate.toPoly support)

private theorem split_certificate {support separant : CBivariate F} (hsupport : support ≠ 0)
    (hprimitive : (CBivariate.toPoly support).IsPrimitive)
    (hsquarefree : Squarefree (CBivariate.toPoly support)) :
    ∃ discarded regular, SplitCertificate support separant discarded regular := by
  classical
  let discarded := globalGcd support separant
  have hdiscarded : discarded ≠ 0 := globalGcd_ne_zero support separant hsupport
  obtain ⟨regular, hquotient⟩ := quotientPrimitive_eq_some_of_dvd hdiscarded
    (globalGcd_dvd support separant hsupport).1
  have hregular : regular ≠ 0 := quotientPrimitive_ne_zero hsupport hquotient
  have hdiscardedPrimitive : (CBivariate.toPoly discarded).IsPrimitive :=
    globalGcd_isPrimitive support separant hsupport
  have hregularPrimitive : (CBivariate.toPoly regular).IsPrimitive :=
    quotientPrimitive_isPrimitive support discarded regular hquotient hregular
  obtain ⟨q, _hq, hregularAssociated, hfactor⟩ := quotientPrimitive_localized hquotient
  have hlocalizedAssociated : Associated
      (ClearDenominators.valueGlobal discarded * ClearDenominators.valueGlobal regular)
      (ClearDenominators.valueGlobal support) := by
    exact (Associated.of_eq (mul_comm _ _)).trans
      ((hregularAssociated.mul_right _).trans (Associated.of_eq hfactor))
  have hproductPrimitive :
      (CBivariate.toPoly (discarded * regular)).IsPrimitive := by
    rw [CBivariate.toPoly_mul]
    exact hdiscardedPrimitive.mul hregularPrimitive
  have hproductDvd : CBivariate.toPoly (discarded * regular) ∣
      CBivariate.toPoly support := by
    apply primitive_dvd_of_valueGlobal_dvd hproductPrimitive
    rw [ClearDenominators.valueGlobal_mul]
    exact hlocalizedAssociated.dvd
  have hsupportDvd : CBivariate.toPoly support ∣
      CBivariate.toPoly (discarded * regular) := by
    apply primitive_dvd_of_valueGlobal_dvd hprimitive
    rw [ClearDenominators.valueGlobal_mul]
    exact hlocalizedAssociated.dvd'
  have hreconstruction : Associated
      (CBivariate.toPoly discarded * CBivariate.toPoly regular)
      (CBivariate.toPoly support) := by
    rw [← CBivariate.toPoly_mul]
    exact associated_of_dvd_dvd hproductDvd hsupportDvd
  have hlocalizedSquarefree : Squarefree (ClearDenominators.valueGlobal support) :=
    squarefree_valueGlobal hprimitive hsquarefree
  have hproductSquarefree : Squarefree
      (ClearDenominators.valueGlobal discarded * ClearDenominators.valueGlobal regular) :=
    hlocalizedAssociated.squarefree_iff.mpr hlocalizedSquarefree
  have hcoprimeDR : IsCoprime (ClearDenominators.valueGlobal discarded)
      (ClearDenominators.valueGlobal regular) :=
    (IsRelPrime.of_squarefree_mul hproductSquarefree).isCoprime
  have hregularLocalized : ClearDenominators.valueGlobal regular ≠ 0 := by
    unfold ClearDenominators.valueGlobal
    exact (Polynomial.map_ne_zero_iff (RatFunc.algebraMap_injective F)).mpr
      (toPoly_ne_zero hregular)
  have hregularCoprime : IsCoprime (ClearDenominators.valueGlobal regular)
      (ClearDenominators.valueGlobal separant) := by
    apply EuclideanDomain.isCoprime_of_dvd
    · exact fun hzero => hregularLocalized hzero.1
    · intro z hzNonunit hz0 hzRegular hzSeparant
      have hzSupport : z ∣ ClearDenominators.valueGlobal support := by
        exact hzRegular.trans ((dvd_mul_left _ _).trans hlocalizedAssociated.dvd)
      have hzGcd : z ∣ EuclideanDomain.gcd
          (ClearDenominators.valueGlobal support)
          (ClearDenominators.valueGlobal separant) :=
        EuclideanDomain.dvd_gcd hzSupport hzSeparant
      have hzDiscarded : z ∣ ClearDenominators.valueGlobal discarded :=
        (globalGcd_associated support separant).dvd_iff_dvd_right.mpr hzGcd
      have hzUnit := hcoprimeDR.symm.isUnit_of_dvd' hzRegular hzDiscarded
      exact hzNonunit hzUnit
  have hregularDvd : CBivariate.toPoly regular ∣ CBivariate.toPoly support := by
    exact quotientPrimitive_dvd_left_global support discarded regular hquotient hregular
  refine ⟨discarded, regular, ?_⟩
  exact
    { discarded_eq := rfl
      quotient_eq := hquotient
      discarded_ne_zero := hdiscarded
      regular_ne_zero := hregular
      discarded_dvd_support := (globalGcd_dvd support separant hsupport).1
      discarded_dvd_separant := (globalGcd_dvd support separant hsupport).2
      regular_dvd_support := hregularDvd
      reconstruction := hreconstruction
      regular_isPrimitive := hregularPrimitive
      regular_squarefree := hsquarefree.squarefree_of_dvd hregularDvd
      regular_coprime_separant := hregularCoprime
      regular_natDegree_le := Polynomial.natDegree_le_of_dvd hregularDvd
        (toPoly_ne_zero hsupport)
      regular_degreeX_le := Polynomial.Bivariate.degreeX_le_of_dvd hregularDvd
        (toPoly_ne_zero hsupport) }

/-- At a point where the separant is nonzero, the checked quotient has exactly the roots of the
incoming squarefree support.  No condition is imposed on the projection fiber. -/
theorem SplitCertificate.evalAt_regular_iff {support separant discarded regular : CBivariate F}
    (cert : SplitCertificate support separant discarded regular)
    {K : Type*} [Field K] (embedding : F →+* K) (u v : K)
    (hseparant : evalAt embedding u v separant ≠ 0) :
    evalAt embedding u v regular = 0 ↔ evalAt embedding u v support = 0 := by
  constructor
  · intro hregular
    exact evalAt_zero_of_dvd embedding u v cert.regular_dvd_support hregular
  · intro hsupport
    have hdiscarded : evalAt embedding u v discarded ≠ 0 := by
      intro hz
      exact hseparant
        (evalAt_zero_of_dvd embedding u v cert.discarded_dvd_separant hz)
    have hproduct : evalAt embedding u v (discarded * regular) = 0 :=
      evalAt_zero_of_dvd embedding u v (by
        rw [CBivariate.toPoly_mul]
        exact cert.reconstruction.dvd') hsupport
    rw [evalAt_mul] at hproduct
    exact (mul_eq_zero.mp hproduct).resolve_left hdiscarded

/-- Exact provenance of a returned positive-degree regular part. -/
theorem run_regularPart_provenance (p : ℕ) (inverse : F → F)
    (equation separant : CBivariate F) (data : Data F)
    (hrun : run p inverse equation separant = .regularPart data) :
    equation ≠ 0 ∧
      data.original = equation ∧ data.separant = separant ∧
      data.core = ClearDenominators.primitivePart equation ∧ data.core.natDegree ≠ 0 ∧
      radical p inverse data.core.natDegree data.core = .ok data.support ∧
      data.discarded = globalGcd data.support data.separant ∧
      quotientPrimitive data.support data.discarded = some data.regular ∧
      0 < data.regular.natDegree := by
  unfold run at hrun
  dsimp only at hrun
  split at hrun
  · cases hrun
  · rename_i hequation
    split at hrun
    · cases hrun
    · rename_i hdegree
      split at hrun
      · cases hrun
      · rename_i support hradical
        unfold finish at hrun
        dsimp only at hrun
        split at hrun
        · cases hrun
        · rename_i regular hquotient
          split at hrun
          · cases hrun
          · rename_i hregularDegree
            cases hrun
            refine ⟨?_, rfl, rfl, rfl, ?_, hradical, rfl, hquotient, ?_⟩
            · simpa only [beq_iff_eq] using hequation
            · simpa only [beq_iff_eq] using hdegree
            · exact Nat.pos_of_ne_zero (by simpa only [beq_iff_eq] using hregularDegree)

/-- Complete semantic contract of a returned nonconstant regular part. -/
structure Certificate (p : ℕ) (inverse : F → F) (equation separant : CBivariate F)
    (data : Data F) : Prop where
  equation_ne_zero : equation ≠ 0
  original_eq : data.original = equation
  separant_eq : data.separant = separant
  core_eq : data.core = ClearDenominators.primitivePart equation
  core_positive : 0 < data.core.natDegree
  radical_execution : radical p inverse data.core.natDegree data.core = .ok data.support
  radical_certificate : RadicalCorrectness.Certificate data.core.natDegree data.core data.support
  split_certificate : SplitCertificate data.support data.separant data.discarded data.regular
  regular_positive : 0 < data.regular.natDegree

/-- Every returned nonconstant result carries radical, gcd, exact-division, squarefreeness,
coprimality, degree, and global reconstruction certificates. -/
theorem run_regularPart_certificate (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (equation separant : CBivariate F) (data : Data F)
    (hinverse : p ≤ (ClearDenominators.primitivePart equation).natDegree →
      ∀ a, inverse a ^ p = a)
    (hrun : run p inverse equation separant = .regularPart data) :
    Certificate p inverse equation separant data := by
  classical
  obtain ⟨hequation, horiginal, hseparant, hcore, hcoreDegree, hradical,
      hdiscarded, hquotient, hregularDegree⟩ :=
    run_regularPart_provenance p inverse equation separant data hrun
  have hcoreNe : data.core ≠ 0 := by
    rw [hcore]
    exact primitivePart_ne_zero hequation
  have hcorePrimitive : (CBivariate.toPoly data.core).IsPrimitive := by
    rw [hcore]
    exact primitivePart_isPrimitive hequation
  have hdegreeBound : (CBivariate.toPoly data.core).natDegree ≤ data.core.natDegree := by
    rw [← RadicalCorrectness.stored_natDegree_eq]
  obtain ⟨support, hradical', hsupportCert⟩ := RadicalCorrectness.radical_certificate
    p data.core.natDegree inverse (by simpa [hcore] using hinverse) data.core hcoreNe
    hcorePrimitive hdegreeBound hcoreDegree
  have hsupport : support = data.support := by
    rw [hradical] at hradical'
    exact (Except.ok.inj hradical').symm
  subst support
  obtain ⟨discarded, regular, hsplit⟩ := split_certificate
    hsupportCert.output_ne_zero hsupportCert.output_isPrimitive hsupportCert.output_squarefree
  have hdiscarded' : discarded = data.discarded := by
    rw [hsplit.discarded_eq, hdiscarded]
  subst discarded
  have hregular : regular = data.regular := by
    have h := hsplit.quotient_eq
    rw [hquotient] at h
    exact (Option.some.inj h).symm
  subst regular
  exact
    { equation_ne_zero := hequation
      original_eq := horiginal
      separant_eq := hseparant
      core_eq := hcore
      core_positive := Nat.pos_of_ne_zero hcoreDegree
      radical_execution := hradical
      radical_certificate := hsupportCert
      split_certificate := hsplit
      regular_positive := hregularDegree }

/-- The returned regular part is a genuine global divisor of the supplied equation. -/
theorem Certificate.regular_dvd_equation {p : ℕ} {inverse : F → F}
    {equation separant : CBivariate F} {data : Data F}
    (cert : Certificate p inverse equation separant data) :
    CBivariate.toPoly data.regular ∣ CBivariate.toPoly equation :=
  cert.split_certificate.regular_dvd_support.trans <|
    cert.radical_certificate.output_dvd_input.trans <| by
      rw [cert.core_eq]
      exact primitivePart_dvd

/-- The returned regular part remains squarefree after embedding the outer polynomial into the
function field in the first variable. -/
theorem Certificate.regular_squarefree_valueGlobal {p : ℕ} {inverse : F → F}
    {equation separant : CBivariate F} {data : Data F}
    (cert : Certificate p inverse equation separant data) :
    Squarefree (ClearDenominators.valueGlobal data.regular) :=
  squarefree_valueGlobal cert.split_certificate.regular_isPrimitive
    cert.split_certificate.regular_squarefree

/-- Both bivariate degrees of the returned regular part are bounded by the original specialized
equation. -/
theorem Certificate.degree_bounds {p : ℕ} {inverse : F → F}
    {equation separant : CBivariate F} {data : Data F}
    (cert : Certificate p inverse equation separant data) :
    (CBivariate.toPoly data.regular).natDegree ≤ (CBivariate.toPoly equation).natDegree ∧
      Polynomial.Bivariate.degreeX (CBivariate.toPoly data.regular) ≤
        Polynomial.Bivariate.degreeX (CBivariate.toPoly equation) :=
  degree_bounds_of_dvd cert.equation_ne_zero cert.regular_dvd_equation

/-- Every root of the primitive core on which the actual separant is nonzero survives the
computed radical and gcd quotient, over every extension field. -/
theorem Certificate.evalAt_regular_of_core {p : ℕ} {inverse : F → F}
    {equation separant : CBivariate F} {data : Data F}
    (cert : Certificate p inverse equation separant data)
    {K : Type*} [Field K] (embedding : F →+* K) (u v : K)
    (hcore : evalAt embedding u v data.core = 0)
    (hseparant : evalAt embedding u v data.separant ≠ 0) :
    evalAt embedding u v data.regular = 0 := by
  let _ : DecidableEq F := instDecidableEqOfLawfulBEq
  have hpower : evalAt embedding u v (data.support ^ data.core.natDegree) = 0 :=
    evalAt_zero_of_dvd embedding u v (by
      rw [show CBivariate.toPoly (data.support ^ data.core.natDegree) =
        CBivariate.toPoly data.support ^ data.core.natDegree from
          map_pow CBivariate.ringEquiv _ _]
      exact cert.radical_certificate.input_dvd_output_pow) hcore
  rw [evalAt_pow] at hpower
  have hsupport : evalAt embedding u v data.support = 0 :=
    (pow_eq_zero_iff cert.core_positive.ne').mp hpower
  exact (cert.split_certificate.evalAt_regular_iff embedding u v hseparant).mpr hsupport

/-- A regular point of the original equation lies on its primitive core.  Pure first-variable
content cannot vanish there because it also divides the actual outer-variable derivative. -/
theorem evalAt_primitivePart_eq_zero_of_regular_point
    (equation : CBivariate F) {K : Type*} [Field K] (embedding : F →+* K) (u v : K)
    (hequation : evalAt embedding u v equation = 0)
    (hseparant : evalAt embedding u v (CBivariate.partialDerivY equation) ≠ 0) :
    evalAt embedding u v (ClearDenominators.primitivePart equation) = 0 := by
  classical
  let content := ClearDenominators.primitiveContent equation
  let core : CBivariate F := ClearDenominators.primitivePart equation
  let lifted : CBivariate F := CPolynomial.C content
  have hfactor : lifted * core = equation := by
    exact ClearDenominators.content_mul_primitivePart equation
  have hconstantDerivative :
      CBivariate.partialDerivY lifted = 0 := by
    apply CPolynomial.toPoly_injective
    unfold CBivariate.partialDerivY
    dsimp only [lifted]
    rw [CPolynomial.derivative_toPoly, CPolynomial.C_toPoly,
      Polynomial.derivative_C, CPolynomial.toPoly_zero]
  have hderivative : CBivariate.partialDerivY equation =
      lifted * CBivariate.partialDerivY core := by
    rw [← hfactor, CBivariate.partialDerivY_mul, hconstantDerivative,
      MulZeroClass.zero_mul, zero_add]
  have hcontent : evalAt embedding u v lifted ≠ 0 := by
    intro hz
    apply hseparant
    rw [hderivative, evalAt_mul, hz, MulZeroClass.zero_mul]
  have hproduct : evalAt embedding u v
      (lifted * core) = 0 := by
    rw [hfactor]
    exact hequation
  rw [evalAt_mul] at hproduct
  exact (mul_eq_zero.mp hproduct).resolve_left hcontent

/-- Every regular point of the original specialized equation is retained by an actually returned
regular part.  The theorem has no projection-discriminant or denominator-fiber premise. -/
theorem Certificate.evalAt_regular_of_equation {p : ℕ} {inverse : F → F}
    {equation separant : CBivariate F} {data : Data F}
    (cert : Certificate p inverse equation separant data)
    {K : Type*} [Field K] (embedding : F →+* K) (u v : K)
    (hactual : separant = CBivariate.partialDerivY equation)
    (hequation : evalAt embedding u v equation = 0)
    (hseparant : evalAt embedding u v separant ≠ 0) :
    evalAt embedding u v data.regular = 0 := by
  apply cert.evalAt_regular_of_core embedding u v
  · rw [cert.core_eq]
    exact evalAt_primitivePart_eq_zero_of_regular_point equation embedding u v hequation
      (by simpa only [hactual] using hseparant)
  · simpa only [cert.separant_eq] using hseparant

private theorem evalAt_ne_zero_of_primitive_natDegree_zero
    {h : CBivariate F} (hprimitive : (CBivariate.toPoly h).IsPrimitive)
    (hdegree : h.natDegree = 0) {K : Type*} [Field K]
    (embedding : F →+* K) (u v : K) : evalAt embedding u v h ≠ 0 := by
  classical
  have hpolyDegree : (CBivariate.toPoly h).natDegree = 0 := by
    simpa only [← RadicalCorrectness.stored_natDegree_eq] using hdegree
  have heq : CBivariate.toPoly h = Polynomial.C ((CBivariate.toPoly h).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hpolyDegree
  have hunit : IsUnit ((CBivariate.toPoly h).coeff 0) :=
    hprimitive _ ⟨1, by simpa only [mul_one] using heq⟩
  rw [evalAt, heq, Polynomial.eval₂_C]
  exact (hunit.map (Polynomial.eval₂RingHom embedding u)).ne_zero

/-- The empty output is semantically exact: when the supplied separant is the actual
outer-variable derivative, no regular point of the original equation exists. -/
theorem run_emptyRegularPart_no_regular_point
    (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (equation separant : CBivariate F) (data : Data F)
    (hequation : equation ≠ 0)
    (hinverse : p ≤ (ClearDenominators.primitivePart equation).natDegree →
      ∀ a, inverse a ^ p = a)
    (hactual : separant = CBivariate.partialDerivY equation)
    (hrun : run p inverse equation separant = .emptyRegularPart data)
    {K : Type*} [Field K] (embedding : F →+* K) (u v : K) :
    ¬ (evalAt embedding u v equation = 0 ∧ evalAt embedding u v separant ≠ 0) := by
  classical
  rintro ⟨hequationRoot, hseparant⟩
  let core : CBivariate F := ClearDenominators.primitivePart equation
  have hcoreNe : core ≠ 0 := primitivePart_ne_zero hequation
  have hcorePrimitive : (CBivariate.toPoly core).IsPrimitive :=
    primitivePart_isPrimitive hequation
  have hcoreRoot : evalAt embedding u v core = 0 := by
    exact evalAt_primitivePart_eq_zero_of_regular_point equation embedding u v hequationRoot
      (by simpa only [hactual] using hseparant)
  by_cases hcoreDegree : core.natDegree = 0
  · exact (evalAt_ne_zero_of_primitive_natDegree_zero hcorePrimitive hcoreDegree
      embedding u v) hcoreRoot
  · have hdegreeBound : (CBivariate.toPoly core).natDegree ≤ core.natDegree := by
      rw [← RadicalCorrectness.stored_natDegree_eq]
    obtain ⟨support, hradical, hsupportCert⟩ := RadicalCorrectness.radical_certificate
      p core.natDegree inverse (by simpa [core] using hinverse) core hcoreNe hcorePrimitive
      hdegreeBound hcoreDegree
    have hrunFinish : finish equation separant core support = .emptyRegularPart data := by
      rw [run] at hrun
      rw [if_neg (by simpa only [beq_iff_eq] using hequation)] at hrun
      dsimp only at hrun
      rw [if_neg (by simpa only [core, beq_iff_eq] using hcoreDegree)] at hrun
      rw [show ClearDenominators.primitivePart equation = core from rfl, hradical] at hrun
      exact hrun
    obtain ⟨discarded, regular, hsplit⟩ := split_certificate
      hsupportCert.output_ne_zero hsupportCert.output_isPrimitive hsupportCert.output_squarefree
    have hfinish : finish equation separant core support =
        if regular.natDegree == 0 then
          .emptyRegularPart ⟨equation, separant, core, support, discarded, regular⟩
        else .regularPart ⟨equation, separant, core, support, discarded, regular⟩ := by
      unfold finish
      dsimp only
      rw [← hsplit.discarded_eq, hsplit.quotient_eq]
    have hregularDegree : regular.natDegree = 0 := by
      rw [hfinish] at hrunFinish
      split at hrunFinish
      · simpa only [beq_iff_eq] using ‹(regular.natDegree == 0) = true›
      · cases hrunFinish
    have hsupportPower : evalAt embedding u v (support ^ core.natDegree) = 0 :=
      evalAt_zero_of_dvd embedding u v (by
        rw [show CBivariate.toPoly (support ^ core.natDegree) =
          CBivariate.toPoly support ^ core.natDegree from map_pow CBivariate.ringEquiv _ _]
        exact hsupportCert.input_dvd_output_pow) hcoreRoot
    rw [evalAt_pow] at hsupportPower
    have hsupportRoot : evalAt embedding u v support = 0 :=
      (pow_eq_zero_iff hcoreDegree).mp hsupportPower
    have hregularRoot : evalAt embedding u v regular = 0 :=
      (hsplit.evalAt_regular_iff embedding u v hseparant).mpr hsupportRoot
    exact (evalAt_ne_zero_of_primitive_natDegree_zero hsplit.regular_isPrimitive
      hregularDegree embedding u v) hregularRoot

/-- A nonzero positive-degree input reaches a computed radical and a successful exact quotient.
No arithmetic failure branch remains under the actual characteristic and inverse-Frobenius law. -/
theorem run_success (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (equation separant : CBivariate F) (hequation : equation ≠ 0)
    (hinverse : p ≤ (ClearDenominators.primitivePart equation).natDegree →
      ∀ a, inverse a ^ p = a) :
    (∃ data, run p inverse equation separant = .emptyRegularPart data) ∨
      (∃ data, run p inverse equation separant = .regularPart data) := by
  classical
  let core := ClearDenominators.primitivePart equation
  have hcore : core ≠ 0 := primitivePart_ne_zero hequation
  by_cases hdegree : core.natDegree = 0
  · left
    refine ⟨⟨equation, separant, core, 1, 1, 1⟩, ?_⟩
    simp [run, hequation, core, hdegree]
  · have hprimitive : (CBivariate.toPoly core).IsPrimitive :=
      primitivePart_isPrimitive hequation
    have hdegreeBound : (CBivariate.toPoly core).natDegree ≤ core.natDegree := by
      rw [← RadicalCorrectness.stored_natDegree_eq]
    obtain ⟨support, hradical, hsupport⟩ := RadicalCorrectness.radical_certificate
      p core.natDegree inverse (by simpa [core] using hinverse) core hcore hprimitive
      hdegreeBound hdegree
    obtain ⟨discarded, regular, hsplit⟩ := split_certificate
      hsupport.output_ne_zero hsupport.output_isPrimitive hsupport.output_squarefree
    have hfinish : finish equation separant core support =
        if regular.natDegree == 0 then
          .emptyRegularPart ⟨equation, separant, core, support, discarded, regular⟩
        else .regularPart ⟨equation, separant, core, support, discarded, regular⟩ := by
      unfold finish
      dsimp only
      rw [← hsplit.discarded_eq, hsplit.quotient_eq]
    rw [run]
    rw [if_neg (by simpa only [beq_iff_eq] using hequation)]
    dsimp only
    rw [if_neg (by simpa only [core, beq_iff_eq] using hdegree)]
    rw [show ClearDenominators.primitivePart equation = core from rfl, hradical]
    dsimp only
    rw [hfinish]
    by_cases hr : regular.natDegree = 0
    · left
      refine ⟨⟨equation, separant, core, support, discarded, regular⟩, ?_⟩
      simp [hr]
    · right
      refine ⟨⟨equation, separant, core, support, discarded, regular⟩, ?_⟩
      simp [hr]

end Polynomial.FunctionFieldAlgorithms.RegularPart

end
